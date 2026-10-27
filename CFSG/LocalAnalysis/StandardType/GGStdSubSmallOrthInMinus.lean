module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthInPlus

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix TableBSymp TableBOrth

open scoped commutatorElement

namespace SmallOrth

section MinusToral

variable {K : Type} [Field K] {m : ℕ}

@[expose] noncomputable def dgHomM (K : Type) [Field K] (m : ℕ) :
    (Fin m → Kˣ) →* GL (LargeEvenMinusIdx m) K :=
  blockInl.comp (dgHom K m)

theorem dgHomM_apply (u : Fin m → Kˣ) :
    dgHomM K m u = TauCeti.diagGL (Sum.elim (pairedUnits u) 1) := blockInl_diagGL _

theorem dgHomM_injective : Function.Injective (dgHomM K m) :=
  blockInl_injective.comp dgHom_injective

def IsFullTorusM (p : ℕ) (A : Subgroup (GL (LargeEvenMinusIdx m) K)) : Prop :=
  (∀ x ∈ A, ∃ u : Fin m → Kˣ, (∀ k, u k ^ p = 1) ∧ dgHomM K m u = x) ∧
    ∀ u : Fin m → Kˣ, (∀ k, u k ^ p = 1) → dgHomM K m u ∈ A

theorem exists_zpow_of_mem_zpowersM {α w : Fin m → Kˣ}
    (h : dgHomM K m w ∈ Subgroup.zpowers (dgHomM K m α)) : ∃ s : ℤ, ∀ k, w k = α k ^ s := by
  obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp h
  have : α ^ s = w := dgHomM_injective (by rw [map_zpow]; exact hs)
  exact ⟨s, fun k => by rw [← this]; rfl⟩

theorem torM_map (F : Kˣ → Kˣ) (hF : ∀ t, F t⁻¹ = (F t)⁻¹) (hF1 : F 1 = 1) (u : Fin m → Kˣ) :
    (Sum.elim (pairedUnits fun k => F (u k)) 1 : LargeEvenMinusIdx m → Kˣ) =
      fun y => F (Sum.elim (pairedUnits u) 1 y) := by
  funext y
  rcases y with (k | k) | t
  · rfl
  · simp [pairedUnits, hF]
  · simp [hF1]

theorem minus_two_class {p : ℕ} (hp : p.Prime) {Ω A D : Subgroup (GL (LargeEvenMinusIdx m) K)}
    {α : Fin m → Kˣ} (hT : IsFullTorusM p A) (hα : ∀ k, α k ^ p = 1)
    (hE : EndData p Ω A D (dgHomM K m α)) {i j : Fin m} (hi : α i ≠ 1) (hj : α j ≠ 1) :
    α j = α i ∨ α j = (α i)⁻¹ := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨hj1, hj2⟩ := hne
  set ν := α i with hν
  set F : Kˣ → Kˣ := fun t => if t = ν ∨ t = ν⁻¹ then t else 1 with hF
  have hFinv : ∀ t, F t⁻¹ = (F t)⁻¹ := by
    intro t
    by_cases h : t = ν ∨ t = ν⁻¹
    · have h' : t⁻¹ = ν ∨ t⁻¹ = ν⁻¹ := by
        rcases h with h | h
        · exact Or.inr (by rw [h])
        · exact Or.inl (by rw [h, inv_inv])
      simp only [hF, if_pos h, if_pos h']
    · have h' : ¬ (t⁻¹ = ν ∨ t⁻¹ = ν⁻¹) := by
        rintro (h' | h')
        · exact h (Or.inr (by rw [← h', inv_inv]))
        · exact h (Or.inl (by rw [← inv_inv t, h', inv_inv]))
      simp only [hF, if_neg h, if_neg h', inv_one]
  have hF1 : F 1 = 1 := by simp only [hF]; split_ifs <;> rfl
  have hFp : ∀ t : Kˣ, t ^ p = 1 → F t ^ p = 1 := by
    intro t ht
    by_cases h : t = ν ∨ t = ν⁻¹
    · simp only [hF, if_pos h, ht]
    · simp only [hF, if_neg h, one_pow]
  set w : Fin m → Kˣ := fun k => F (α k) with hw
  have hwp : ∀ k, w k ^ p = 1 := fun k => hFp _ (hα k)
  have hxA : dgHomM K m w ∈ A := hT.2 w hwp
  have hcomm : ∀ d ∈ D, dgHomM K m w * d = d * dgHomM K m w := by
    intro d hd
    have hda := hE.D_cent d hd
    rw [dgHomM_apply] at hda
    have hw' : (Sum.elim (pairedUnits w) 1 : LargeEvenMinusIdx m → Kˣ) =
        fun y => F (Sum.elim (pairedUnits α) 1 y) := torM_map F hFinv hF1 α
    rw [dgHomM_apply]
    refine commute_of_function (δ := Sum.elim (pairedUnits α) 1)
      (ε := Sum.elim (pairedUnits w) 1) (fun y z hyz => ?_) hda
    rw [hw']
    show F (Sum.elim (pairedUnits α) 1 y) = F (Sum.elim (pairedUnits α) 1 z)
    rw [hyz]
  obtain ⟨s, hs⟩ := exists_zpow_of_mem_zpowersM (hE.A_cent _ hxA hcomm)
  have hFν : F ν = ν := by simp [hF]
  have hFj : F (α j) = 1 := by
    have : ¬ (α j = ν ∨ α j = ν⁻¹) := fun h => h.elim hj1 hj2
    simp only [hF, if_neg this]
  have hwi : w i = ν := hFν
  have hwj : w j = 1 := hFj
  have h1 : ν ^ s = ν := by rw [← hs i, hwi]
  have h2 : α j ^ s = α j := zpow_eq_self_of_order hp (hα i) hi (hα j) hj h1
  have h3 : α j = 1 := by rw [← h2, ← hs j, hwj]
  exact hj h3

theorem minus_dichotomy {p : ℕ} (hp : p.Prime) {Ω A D : Subgroup (GL (LargeEvenMinusIdx m) K)}
    {α : Fin m → Kˣ} (hT : IsFullTorusM p A) (hα : ∀ k, α k ^ p = 1)
    (hE : EndData p Ω A D (dgHomM K m α)) :
    (∃ i₀, α i₀ ≠ 1 ∧ ∀ k, k ≠ i₀ → α k = 1) ∨ ∀ k, α k ≠ 1 := by
  classical
  have hex : ∃ i₀, α i₀ ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hE.a_ne
    have : α = 1 := funext hall
    rw [this, map_one]
  obtain ⟨i₀, hi₀⟩ := hex
  have ha : dgHomM K m α = TauCeti.diagGL (Sum.elim (pairedUnits α) 1) := dgHomM_apply α
  set δ : LargeEvenMinusIdx m → Kˣ := Sum.elim (pairedUnits α) 1 with hδ
  set C : Subgroup (GL (LargeEvenMinusIdx m) K) := Ω ⊓ Subgroup.centralizer {dgHomM K m α}
    with hC
  have hDC : D ≤ C := fun d hd =>
    ⟨hE.D_le hd, Subgroup.mem_centralizer_singleton_iff.mpr (hE.D_cent d hd)⟩
  have hBC : fixStar Ω δ ≤ C := fun g hg =>
    ⟨hg.1, Subgroup.mem_centralizer_singleton_iff.mpr (by rw [ha]; exact hg.2.1)⟩
  have hDn : ∀ c ∈ C, ∀ d ∈ D, c * d * c⁻¹ ∈ D := fun c hc d hd =>
    hE.D_norm c hc.1 (Subgroup.mem_centralizer_singleton_iff.mp hc.2) d hd
  have hBn : ∀ c ∈ C, ∀ b ∈ fixStar Ω δ, c * b * c⁻¹ ∈ fixStar Ω δ := fun c hc b hb =>
    fixStar_normal hc.1 (by rw [← ha]; exact Subgroup.mem_centralizer_singleton_iff.mp hc.2) hb
  have hi₀p := hα i₀
  rcases commute_or_le hDC hBC hDn hBn hE.D_qs with hle | hcomm
  ·
    left
    refine ⟨i₀, hi₀, fun j hj => ?_⟩
    by_contra hj1
    set x : GL (LargeEvenMinusIdx m) K := dgHomM K m (Pi.mulSingle i₀ (α i₀)) with hx
    have hxp : ∀ k, (Pi.mulSingle i₀ (α i₀) : Fin m → Kˣ) k ^ p = 1 := by
      intro k
      by_cases hk : k = i₀
      · subst hk
        rw [Pi.mulSingle_eq_same]
        exact hi₀p
      · rw [Pi.mulSingle_eq_of_ne hk, one_pow]
    have hxA : x ∈ A := hT.2 _ hxp
    have hxD : ∀ d ∈ D, x * d = d * x := by
      intro d hd
      rw [hx, dgHomM_apply]
      refine commute_of_fixStar (δ := δ) (ε := Sum.elim (pairedUnits (Pi.mulSingle i₀ (α i₀))) 1)
        ?_ (hle hd)
      intro y hy
      rcases y with (k | k) | t
      · have hk : α k = 1 := hy
        have hki : k ≠ i₀ := fun h => hi₀ (h ▸ hk)
        simp [pairedUnits, Pi.mulSingle_eq_of_ne hki]
      · have hk : (α k)⁻¹ = 1 := hy
        have hk' : α k = 1 := inv_eq_one.mp hk
        have hki : k ≠ i₀ := fun h => hi₀ (h ▸ hk')
        simp [pairedUnits, Pi.mulSingle_eq_of_ne hki]
      · rfl
    obtain ⟨s, hs⟩ := exists_zpow_of_mem_zpowersM (hE.A_cent x hxA hxD)
    have h1 : α i₀ ^ s = α i₀ := by rw [← hs i₀, Pi.mulSingle_eq_same]
    have h2 : α j ^ s = α j := zpow_eq_self_of_order hp hi₀p hi₀ (hα j) hj1 h1
    have h3 : α j = 1 := by
      rw [← h2, ← hs j, Pi.mulSingle_eq_of_ne hj]
    exact hj1 h3
  ·
    right
    intro k hk
    set x : GL (LargeEvenMinusIdx m) K := dgHomM K m (Pi.mulSingle k (α i₀)) with hx
    have hxp : ∀ k', (Pi.mulSingle k (α i₀) : Fin m → Kˣ) k' ^ p = 1 := by
      intro k'
      by_cases hk' : k' = k
      · subst hk'
        rw [Pi.mulSingle_eq_same]
        exact hi₀p
      · rw [Pi.mulSingle_eq_of_ne hk', one_pow]
    have hxA : x ∈ A := hT.2 _ hxp
    have hxB : x ∈ fixStar Ω δ := by
      refine ⟨hE.A_le hxA, ?_, ?_⟩
      · rw [← ha, hx, ← map_mul, ← map_mul, mul_comm]
      · rw [hx, dgHomM_apply]
        refine diag_mul_pStar (δ := δ) (ε := Sum.elim (pairedUnits (Pi.mulSingle k (α i₀))) 1) ?_
        intro y hy
        rcases y with (k' | k') | t
        · have hk' : k' ≠ k := fun h => hy (h ▸ hk)
          simp [pairedUnits, Pi.mulSingle_eq_of_ne hk']
        · have hk' : k' ≠ k := fun h => hy (by simp [hδ, pairedUnits, h, hk])
          simp [pairedUnits, Pi.mulSingle_eq_of_ne hk']
        · rfl
    have hxD : ∀ d ∈ D, x * d = d * x := fun d hd => (hcomm d hd x hxB).symm
    obtain ⟨s, hs⟩ := exists_zpow_of_mem_zpowersM (hE.A_cent x hxA hxD)
    have h1 : α i₀ = 1 := by
      have := hs k
      rwa [Pi.mulSingle_eq_same, hk, _root_.one_zpow] at this
    exact hi₀ h1

theorem IsFullTorusM.map_conj {p : ℕ} {A : Subgroup (GL (LargeEvenMinusIdx m) K)}
    (hT : IsFullTorusM p A) (s : GL (LargeEvenMinusIdx m) K)
    (τ : (Fin m → Kˣ) → Fin m → Kˣ)
    (hτ : ∀ u, s * dgHomM K m u * s⁻¹ = dgHomM K m (τ u))
    (hτp : ∀ u : Fin m → Kˣ, (∀ k, u k ^ p = 1) → ∀ k, τ u k ^ p = 1)
    (hτs : ∀ u' : Fin m → Kˣ, (∀ k, u' k ^ p = 1) → ∃ u : Fin m → Kˣ,
      (∀ k, u k ^ p = 1) ∧ τ u = u') :
    IsFullTorusM p (A.map (MulAut.conj s).toMonoidHom) := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hT.1 x hx
    exact ⟨τ u, hτp u hu, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hτ]⟩
  · intro u' hu'
    obtain ⟨u, hu, rfl⟩ := hτs u' hu'
    exact ⟨dgHomM K m u, hT.2 u hu, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hτ]⟩

theorem conj_dgHomM_perm (σ : Equiv.Perm (Fin m)) (u : Fin m → Kˣ) :
    blockInl (TauCeti.permutationGL (k := K) (Equiv.Perm.sumCongr σ σ)) * dgHomM K m u *
        (blockInl (TauCeti.permutationGL (k := K) (Equiv.Perm.sumCongr σ σ)))⁻¹ =
      dgHomM K m (fun k => u (σ⁻¹ k)) := by
  rw [← map_inv]
  change blockInl _ * blockInl (dgHom K m u) * blockInl _ = blockInl (dgHom K m _)
  rw [← map_mul, ← map_mul, conj_dgHom_perm]

theorem conj_dgHomM_swapOn (F : Fin m → Prop) [DecidablePred F] (u : Fin m → Kˣ) :
    blockInl (TauCeti.permutationGL (k := K) (swapOn F)) * dgHomM K m u *
        (blockInl (TauCeti.permutationGL (k := K) (swapOn F)))⁻¹ =
      dgHomM K m (fun k => if F k then (u k)⁻¹ else u k) := by
  rw [← map_inv]
  change blockInl _ * blockInl (dgHom K m u) * blockInl _ = blockInl (dgHom K m _)
  rw [← map_mul, ← map_mul, conj_dgHom_swapOn]

theorem blockInl_mem_orth {b c : K} {g : GL (Fin m ⊕ Fin m) K}
    (hg : g ∈ LargeEvenOrthGroup (LargeEvenQPlus K m)) :
    blockInl g ∈ LargeEvenOrthGroup (LargeEvenQMinus m b c) :=
  map_blockInl_orth_le b c ⟨g, hg, rfl⟩

theorem embHom_minusSplit_diag {k : ℕ} (u : Fin (k + 1) → Kˣ) (hu : u (Fin.last k) = 1) :
    embHom (minusSplit k)
        (TauCeti.diagGL (Sum.elim (pairedUnits fun j => u (Fin.castSucc j)) 1)) =
      TauCeti.diagGL (Sum.elim (pairedUnits u) 1) := by
  apply Units.ext
  apply (Matrix.reindex (minusSplit k) (minusSplit k)).injective
  have h1 : (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) = Matrix.diagonal (fun _ => 1) :=
    Matrix.diagonal_one.symm
  rw [reindex_embHom, TauCeti.diagGL_coe, TauCeti.diagGL_coe, Matrix.reindex_apply,
    Matrix.submatrix_diagonal_equiv, h1, Matrix.fromBlocks_diagonal]
  congr 1
  funext z
  rcases z with x | a
  · rcases x with (x | x) | t
    · simp [minusSplit_symm_inl_inl_inl, pairedUnits]
    · simp [minusSplit_symm_inl_inl_inr, pairedUnits]
    · simp [minusSplit_symm_inl_inr]
  · rcases a with a | a
    · simp [minusSplit_symm_inr_inl, pairedUnits, hu]
    · simp [minusSplit_symm_inr_inr, pairedUnits, hu]

@[expose] noncomputable def leviSLM (K : Type) [Field K] (m : ℕ) :
    Matrix.SpecialLinearGroup (Fin m) K →* GL (LargeEvenMinusIdx m) K :=
  blockInl.comp (leviSL K m)

theorem leviSLM_injective : Function.Injective (leviSLM K m) :=
  blockInl_injective.comp leviSL_injective

theorem range_leviSLM_le (hm : 3 ≤ m) (b c : K) :
    (leviSLM K m).range ≤ LargeEvenOmega (LargeEvenQMinus m b c) := by
  rintro _ ⟨s, rfl⟩
  exact blockInl_mem_omegaMinus b c (range_leviSL_le hm ⟨s, rfl⟩)

theorem isQuasisimple_range_leviSLM (hm : 3 ≤ m) : CFSG.IsQuasisimple (leviSLM K m).range :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective leviSLM_injective)
    (isQuasisimple_sl hm)

theorem dgHomM_mem_range_leviSLM (u : Fin m → Kˣ) (hu : ∏ k, ((u k : Kˣ) : K) = 1) :
    dgHomM K m u ∈ (leviSLM K m).range := by
  obtain ⟨s, hs⟩ := dgHom_mem_range_leviSL u hu
  exact ⟨s, by change blockInl (leviSL K m s) = blockInl (dgHom K m u); rw [hs]⟩

theorem leviSLM_commute (ν : Kˣ) (s : Matrix.SpecialLinearGroup (Fin m) K) :
    leviSLM K m s * dgHomM K m (fun _ => ν) = dgHomM K m (fun _ => ν) * leviSLM K m s := by
  change blockInl (leviHom K m (Matrix.SpecialLinearGroup.toGL s)) * blockInl (dgHom K m _) =
    blockInl (dgHom K m _) * blockInl (leviHom K m (Matrix.SpecialLinearGroup.toGL s))
  rw [← map_mul, ← map_mul, leviHom_commute]

theorem exists_blockForm {ν : Kˣ} (hν1 : ν ≠ 1) {b c : K} {g : GL (LargeEvenMinusIdx m) K}
    (hgc : g * dgHomM K m (fun _ => ν) = dgHomM K m (fun _ => ν) * g)
    (hgO : g ∈ LargeEvenOrthGroup (LargeEvenQMinus m b c)) :
    ∃ (G : GL (Fin m ⊕ Fin m) K) (G₂ : Matrix (Fin 2) (Fin 2) K),
      G ∈ LargeEvenOrthGroup (LargeEvenQPlus K m) ∧
      G * dgHom K m (fun _ => ν) = dgHom K m (fun _ => ν) * G ∧
      (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) =
        Matrix.fromBlocks (G : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) 0 0 G₂ := by
  rw [dgHomM_apply] at hgc
  have hm := commute_diagGL_iff.mp hgc
  set M : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K :=
    (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) with hM
  have hne1 : ((ν : Kˣ) : K) ≠ 1 := fun h => hν1 (Units.ext h)
  have hne1' : ((ν⁻¹ : Kˣ) : K) ≠ 1 := fun h => hν1 (inv_eq_one.mp (Units.ext h))
  have h₁₂ : M.toBlocks₁₂ = 0 := by
    ext y t
    rcases y with i | i
    · exact eq_zero_of_commute_diagonal hm (i := Sum.inl (Sum.inl i)) (j := Sum.inr t)
        (by simpa [pairedUnits] using hne1)
    · exact eq_zero_of_commute_diagonal hm (i := Sum.inl (Sum.inr i)) (j := Sum.inr t)
        (by simpa [pairedUnits] using hne1')
  have h₂₁ : M.toBlocks₂₁ = 0 := by
    ext t y
    rcases y with i | i
    · exact eq_zero_of_commute_diagonal hm (i := Sum.inr t) (j := Sum.inl (Sum.inl i))
        (by simpa [pairedUnits] using hne1.symm)
    · exact eq_zero_of_commute_diagonal hm (i := Sum.inr t) (j := Sum.inl (Sum.inr i))
        (by simpa [pairedUnits] using hne1'.symm)
  obtain ⟨G₁, G₂, hblock⟩ : ∃ (G₁ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
      (G₂ : Matrix (Fin 2) (Fin 2) K), M = Matrix.fromBlocks G₁ 0 0 G₂ := by
    refine ⟨M.toBlocks₁₁, M.toBlocks₂₂, ?_⟩
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    rw [h₁₂, h₂₁]
  have hD : (Matrix.diagonal fun y : LargeEvenMinusIdx m =>
      ((Sum.elim (pairedUnits fun _ : Fin m => ν) 1 y : Kˣ) : K)) =
      Matrix.fromBlocks (Matrix.diagonal fun y : Fin m ⊕ Fin m =>
        ((pairedUnits (fun _ : Fin m => ν) y : Kˣ) : K)) 0 0
        (Matrix.diagonal fun _ : Fin 2 => (1 : K)) := by
    rw [Matrix.fromBlocks_diagonal]
    congr 1
    funext y
    rcases y with y | t <;> simp
  have hcomm₁ : G₁ * Matrix.diagonal (fun y : Fin m ⊕ Fin m =>
      ((pairedUnits (fun _ : Fin m => ν) y : Kˣ) : K)) =
      Matrix.diagonal (fun y : Fin m ⊕ Fin m =>
        ((pairedUnits (fun _ : Fin m => ν) y : Kˣ) : K)) * G₁ := by
    rw [hD, hblock, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hm
    have := congrArg Matrix.toBlocks₁₁ hm
    simpa using this
  have hiso : ∀ v₁ : Fin m ⊕ Fin m → K,
      LargeEvenQPlus K m (G₁ *ᵥ v₁) = LargeEvenQPlus K m v₁ := by
    intro v₁
    have := isometry_of_mem_orthGroup hgO (Sum.elim v₁ 0)
    rw [← hM, hblock, Matrix.fromBlocks_mulVec, largeEvenQMinus_eq, largeEvenQMinus_eq] at this
    simpa [Function.comp_def] using this
  have hdet : G₁.det ≠ 0 := by
    have h1 : M.det ≠ 0 := by
      have := (Matrix.GeneralLinearGroup.det g).ne_zero
      rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
    rw [hblock, Matrix.det_fromBlocks_zero₂₁] at h1
    exact left_ne_zero_of_mul h1
  set G := Matrix.GeneralLinearGroup.mkOfDetNeZero G₁ hdet with hG
  have hG1 : (G : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = G₁ :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero G₁ hdet
  refine ⟨G, G₂, mem_orthGroup_of_isometry fun v => by rw [hG1]; exact hiso v, ?_, ?_⟩
  · rw [dgHom_apply]
    exact commute_diagGL_iff.mpr (by rw [hG1]; exact hcomm₁)
  · rw [hG1]
    exact hblock

theorem conj_mem_range_leviSLM {ν : Kˣ} (hν : ν * ν ≠ 1) (hν1 : ν ≠ 1) {b c : K}
    {g : GL (LargeEvenMinusIdx m) K}
    (hgc : g * dgHomM K m (fun _ => ν) = dgHomM K m (fun _ => ν) * g)
    (hgO : g ∈ LargeEvenOrthGroup (LargeEvenQMinus m b c))
    {y : GL (LargeEvenMinusIdx m) K} (hy : y ∈ (leviSLM K m).range) :
    g * y * g⁻¹ ∈ (leviSLM K m).range := by
  obtain ⟨s, rfl⟩ := hy
  obtain ⟨G, G₂, hGO, hGc, hblock⟩ := exists_blockForm hν1 hgc hgO
  obtain ⟨h, rfl⟩ := exists_leviHom_eq hν hGc hGO
  set z : GL (Fin m) K := h * Matrix.SpecialLinearGroup.toGL s * h⁻¹ with hz
  have hdet : Matrix.GeneralLinearGroup.det z = 1 := by
    simp [hz]
  have hmem : z ∈
      (Matrix.SpecialLinearGroup.toGL (n := Fin m) (R := K)).range := by
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet
  obtain ⟨s', hs'⟩ := hmem
  refine ⟨s', ?_⟩
  have hzz : leviHom K m z * leviHom K m h = leviHom K m h * leviHom K m
      (Matrix.SpecialLinearGroup.toGL s) := by
    rw [hz, ← map_mul, ← map_mul]
    congr 1
    group
  have e : g * leviSLM K m s = blockInl (leviHom K m z) * g := by
    apply Units.ext
    have hs1 : ((leviSLM K m s : GL (LargeEvenMinusIdx m) K) :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) =
        Matrix.fromBlocks ((leviHom K m (Matrix.SpecialLinearGroup.toGL s) : GL _ K) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) 0 0 1 := coe_blockInl _
    have hz1 : ((blockInl (leviHom K m z) : GL (LargeEvenMinusIdx m) K) :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) =
        Matrix.fromBlocks ((leviHom K m z : GL _ K) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) 0 0 1 := coe_blockInl _
    rw [Units.val_mul, Units.val_mul, hblock, hs1, hz1, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
      Matrix.one_mul]
    congr 1
    have := congrArg
      (fun x : GL (Fin m ⊕ Fin m) K => (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) hzz
    simpa only [Units.val_mul] using this.symm
  change blockInl (leviHom K m (Matrix.SpecialLinearGroup.toGL s')) =
    g * blockInl (leviHom K m (Matrix.SpecialLinearGroup.toGL s)) * g⁻¹
  rw [hs']
  change _ = g * leviSLM K m s * g⁻¹
  rw [e, mul_inv_cancel_right]

theorem leviHom_diagGL (w : Fin m → Kˣ) :
    leviHom K m (TauCeti.diagGL w) = dgHom K m w := by
  apply Units.ext
  rw [coe_leviHom, coe_dgHom, TauCeti.diagGL_coe]
  congr 1
  rw [← map_inv, TauCeti.diagGL_coe, Matrix.diagonal_transpose]
  rfl

theorem minus_card_two [Finite K] {p : ℕ} (hp : p.Prime) {m : ℕ} (hm : 3 ≤ m) {ν : Kˣ}
    (hνo : orderOf ν = p) {A : Subgroup (GL (LargeEvenMinusIdx m) K)} (hT : IsFullTorusM p A) :
    p ^ 2 ≤ Nat.card ↥(A ⊓ (leviSLM K m).range) := by
  classical
  haveI := Fact.mk hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hνp : ν ^ p = 1 := hνo ▸ pow_orderOf_eq_one ν
  set z : Multiplicative (ZMod p) →* Kˣ := zmodPowHom hνp with hz
  have hzinj : Function.Injective z :=
    (injective_iff_map_eq_one _).2 fun a ha => (zmodPowHom_eq_one_iff hνp hνo).1 ha
  have hzp : ∀ a : Multiplicative (ZMod p), z a ^ p = 1 := fun a => by
    rw [← map_pow]
    have : a ^ p = 1 := by
      rw [← ofAdd_toAdd a, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]
    rw [this, map_one]
  set i0 : Fin m := ⟨0, by omega⟩ with hi0
  set i1 : Fin m := ⟨1, by omega⟩ with hi1
  set i2 : Fin m := ⟨2, by omega⟩ with hi2
  let u : (Fin 2 → Multiplicative (ZMod p)) → Fin m → Kˣ := fun f =>
    tauPair i0 i1 (z (f 0)) * tauPair i1 i2 (z (f 1))
  have hup : ∀ f k, (u f k) ^ p = 1 := by
    intro f k
    simp only [u, Pi.mul_apply, mul_pow, tauPair_pow (hzp _), mul_one]
  have hprod : ∀ f, ∏ k, (((u f k : Kˣ)) : K) = 1 := by
    intro f
    simp only [u, Pi.mul_apply, Units.val_mul, Finset.prod_mul_distrib, prod_tauPair, mul_one]
  have hu0 : ∀ f, u f i0 = z (f 0) := by
    intro f
    simp [u, tauPair, Pi.mulSingle_apply, hi0, hi1, hi2, Fin.ext_iff]
  have hu1 : ∀ f, u f i1 = (z (f 0))⁻¹ * z (f 1) := by
    intro f
    simp [u, tauPair, Pi.mulSingle_apply, hi0, hi1, hi2, Fin.ext_iff]
  have hginj : Function.Injective fun f => dgHomM K m (u f) := by
    intro f f' h
    have huf : u f = u f' := dgHomM_injective h
    have e0 : f 0 = f' 0 := hzinj (by rw [← hu0 f, ← hu0 f', huf])
    have e1' : (z (f 0))⁻¹ * z (f 1) = (z (f' 0))⁻¹ * z (f' 1) := by
      rw [← hu1 f, ← hu1 f', huf]
    have e1 : f 1 = f' 1 := hzinj (by rw [e0] at e1'; exact mul_left_cancel e1')
    funext j
    fin_cases j
    · exact e0
    · exact e1
  exact fin_pow_le_card (A ⊓ (leviSLM K m).range) (fun f => dgHomM K m (u f)) hginj
    fun f => ⟨hT.2 (u f) (hup f), dgHomM_mem_range_leviSLM (u f) (hprod f)⟩

theorem minus_beta_eq [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ}
    (hm : 3 ≤ m) {b c : K} {ν : Kˣ} (hνo : orderOf ν = p)
    {A D : Subgroup (GL (LargeEvenMinusIdx m) K)} (hT : IsFullTorusM p A)
    (hE : EndData p (LargeEvenOmega (LargeEvenQMinus m b c)) A D (dgHomM K m (fun _ => ν))) :
    D = (leviSLM K m).range := by
  classical
  haveI := Fact.mk hp
  have hν1 : ν ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hνo
    exact hp.one_lt.ne hνo
  have hν2 : ν * ν ≠ 1 := by
    intro h
    have h2 : ν ^ 2 = 1 := by rw [sq]; exact h
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hνo] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  set Ω := LargeEvenOmega (LargeEvenQMinus m b c) with hΩ
  set a := dgHomM K m (fun _ => ν) with ha
  set Y : Subgroup (GL (LargeEvenMinusIdx m) K) := (leviSLM K m).range with hY
  have hYΩ : Y ≤ Ω := range_leviSLM_le hm b c
  have hYc : ∀ y ∈ Y, y * a = a * y := by
    rintro _ ⟨s, rfl⟩
    exact leviSLM_commute ν s
  have hYq : CFSG.IsQuasisimple Y := isQuasisimple_range_leviSLM hm
  have hcard : p ^ 2 ≤ Nat.card ↥(A ⊓ Y) := minus_card_two hp hm hνo hT
  set C : Subgroup (GL (LargeEvenMinusIdx m) K) := Ω ⊓ Subgroup.centralizer {a} with hC
  have hDC : D ≤ C := fun d hd =>
    ⟨hE.D_le hd, Subgroup.mem_centralizer_singleton_iff.mpr (hE.D_cent d hd)⟩
  have hYC : Y ≤ C := fun y hy =>
    ⟨hYΩ hy, Subgroup.mem_centralizer_singleton_iff.mpr (hYc y hy)⟩
  have hDn : ∀ c ∈ C, ∀ d ∈ D, c * d * c⁻¹ ∈ D := fun c hc d hd =>
    hE.D_norm c hc.1 (Subgroup.mem_centralizer_singleton_iff.mp hc.2) d hd
  have hYn : ∀ c ∈ C, ∀ y ∈ Y, c * y * c⁻¹ ∈ Y := fun c hc y hy =>
    conj_mem_range_leviSLM hν2 hν1 (Subgroup.mem_centralizer_singleton_iff.mp hc.2)
      (omega_le_orth _ hc.1) hy
  rcases commute_or_le hDC hYC hDn hYn hE.D_qs with hle | hcomm
  · exact StdSubRestThree.eq_of_le_of_quasisimple hle
      (fun b hb d hd => hE.D_norm b (hYΩ hb) (hYc b hb) d hd) hYq hE.D_qs
  · exfalso
    have hsub : A ⊓ Y ≤ Subgroup.zpowers a := fun x hx =>
      hE.A_cent x hx.1 fun d hd => (hcomm d hd x hx.2).symm
    have h1 : Nat.card ↥(A ⊓ Y) ≤ Nat.card ↥(Subgroup.zpowers a) := Subgroup.card_le_of_le hsub
    have h2 : Nat.card ↥(Subgroup.zpowers a) ≤ p := by
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one hp.pos (hE.A_elem.2 a hE.a_mem)
    have h3 : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega

@[expose] noncomputable def xRoot {i j : Fin m} (hij : i ≠ j) :
    Multiplicative K →* GL (LargeEvenMinusIdx m) K :=
  blockInl.comp ((leviHom K m).comp (TauCeti.transvectionHom hij))

theorem xRoot_conj {i j : Fin m} (hij : i ≠ j) (w : Fin m → Kˣ) (c : Multiplicative K) :
    dgHomM K m w * xRoot hij c * (dgHomM K m w)⁻¹ =
      xRoot hij (Multiplicative.ofAdd (((w i : Kˣ) : K) * Multiplicative.toAdd c *
        (((w j)⁻¹ : Kˣ) : K))) := by
  have e : dgHomM K m w = blockInl (leviHom K m (TauCeti.diagGL w)) := by
    change blockInl (dgHom K m w) = _
    rw [leviHom_diagGL]
  rw [e, ← map_inv]
  change blockInl _ * blockInl (leviHom K m (TauCeti.transvectionHom hij c)) * blockInl _ =
    blockInl (leviHom K m (TauCeti.transvectionHom hij _))
  rw [← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul, TauCeti.transvectionHom_apply,
    TauCeti.transvectionHom_apply, TauCeti.diagGL_mul_transvectionUnit_mul_inv]
  simp only [toAdd_ofAdd]

theorem xRoot_injective {i j : Fin m} (hij : i ≠ j) : Function.Injective (xRoot (K := K) hij) :=
  blockInl_injective.comp (leviHom_injective.comp (TauCeti.transvectionHom_injective hij))

theorem xRoot_mem_range {i j : Fin m} (hij : i ≠ j) (c : Multiplicative K) :
    xRoot hij c ∈ (leviSLM K m).range := by
  refine ⟨Matrix.SpecialLinearGroup.transvection hij (Multiplicative.toAdd c), ?_⟩
  change blockInl (leviHom K m (Matrix.SpecialLinearGroup.toGL _)) = xRoot hij c
  rw [TauCeti.toGL_transvection_eq_transvectionUnit]
  change _ = blockInl (leviHom K m (TauCeti.transvectionHom hij c))
  rw [TauCeti.transvectionHom_apply]

theorem xRoot_sq [CharP K 2] {i j : Fin m} (hij : i ≠ j) (c : Multiplicative K) :
    xRoot hij c ^ 2 = 1 := by
  rw [← map_pow]
  have : c ^ 2 = 1 := by
    rw [← ofAdd_toAdd c, ← ofAdd_nsmul, two_nsmul, CharTwo.add_self_eq_zero, ofAdd_zero]
  rw [this, map_one]

theorem minus_beta_three [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ}
    (hm : 3 ≤ m) {b c : K} {ν : Kˣ} (hνo : orderOf ν = p)
    {A D : Subgroup (GL (LargeEvenMinusIdx m) K)} (hT : IsFullTorusM p A)
    (hE : EndData p (LargeEvenOmega (LargeEvenQMinus m b c)) A D (dgHomM K m (fun _ => ν))) :
    NormConcl p A D := by
  classical
  haveI := Fact.mk hp
  have hνp : ν ^ p = 1 := hνo ▸ pow_orderOf_eq_one ν
  have hν2 : ν * ν ≠ 1 := by
    intro h
    have h2 : ν ^ 2 = 1 := by rw [sq]; exact h
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hνo] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  have hDY := minus_beta_eq hp hp2 hm hνo hT hE
  set i0 : Fin m := ⟨0, by omega⟩ with hi0
  set i1 : Fin m := ⟨1, by omega⟩ with hi1
  have hij : i0 ≠ i1 := by simp [hi0, hi1, Fin.ext_iff]
  set U : Subgroup (GL (LargeEvenMinusIdx m) K) := (xRoot (K := K) hij).range with hU
  have hAU : ∀ s ∈ A, ∀ u ∈ U, s * u * s⁻¹ ∈ U := by
    intro s hs u hu
    obtain ⟨w, -, rfl⟩ := hT.1 s hs
    obtain ⟨c', rfl⟩ := hu
    rw [xRoot_conj]
    exact ⟨_, rfl⟩
  set t : GL (LargeEvenMinusIdx m) K := dgHomM K m (tauPair i0 i1 ν) with ht
  have htp' : ∀ k, (tauPair i0 i1 ν k) ^ p = 1 := fun k => tauPair_pow hνp i0 i1 k
  have htA : t ∈ A := hT.2 _ htp'
  have htU : ∀ h ∈ U, t * h * t⁻¹ ∈ U := fun h hh => hAU t htA h hh
  have htU' : ∀ h ∈ U, t⁻¹ * h * t ∈ U := fun h hh => by
    simpa using hAU t⁻¹ (A.inv_mem htA) h hh
  refine NormConcl.intro U (hDY ▸ ?_) ?_ ?_ hAU t (hDY ▸ ?_) ?_ ?_ ?_
    (xRoot hij (Multiplicative.ofAdd 1)) (hDY ▸ xRoot_mem_range hij _) ?_
  · rintro _ ⟨c', rfl⟩
    exact xRoot_mem_range hij c'
  · intro hbot
    have h1 : xRoot hij (Multiplicative.ofAdd (1 : K)) ∈ U := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : Multiplicative.ofAdd (1 : K) = 1 := xRoot_injective hij (by rw [h1, map_one])
    exact one_ne_zero (ofAdd_eq_one.mp h2)
  · intro g
    obtain ⟨c', hc'⟩ := g.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, ← hc']
    simpa using xRoot_sq (K := K) hij c'
  · exact dgHomM_mem_range_leviSLM _ (prod_tauPair i0 i1 ν)
  · rw [ht, ← map_pow]
    have : (tauPair i0 i1 ν) ^ p = 1 := funext fun k => htp' k
    rw [this, map_one]
  · intro s hs
    obtain ⟨w, -, rfl⟩ := hT.1 s hs
    rw [ht, ← map_mul, ← map_mul, mul_comm]
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => htU h hh, fun hh => ?_⟩
    have h5 := htU' _ hh
    have e : t⁻¹ * (t * h * t⁻¹) * t = h := by group
    rwa [e] at h5
  · intro hcomm
    have h1 : t * xRoot hij (Multiplicative.ofAdd 1) * t⁻¹ =
        xRoot hij (Multiplicative.ofAdd 1) := by
      rw [hcomm, mul_inv_cancel_right]
    rw [ht, xRoot_conj] at h1
    have h2 := xRoot_injective hij h1
    have h3 := Multiplicative.ofAdd.injective h2
    apply hν2
    have h4 : ((tauPair i0 i1 ν i0 : Kˣ) : K) * 1 * (((tauPair i0 i1 ν i1)⁻¹ : Kˣ) : K) = 1 := h3
    simp [tauPair, Pi.mulSingle_apply, hi0, hi1, Fin.ext_iff] at h4
    exact Units.ext (by simpa using h4)

theorem minus_alpha_three [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ}
    (hk : 2 ≤ k) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {ζ : Kˣ}
    (hζo : orderOf ζ = p) {A D : Subgroup (GL (LargeEvenMinusIdx (k + 1)) K)}
    (hT : IsFullTorusM p A)
    (hE : EndData p (LargeEvenOmega (LargeEvenQMinus (k + 1) b c)) A D
      (dgHomM K (k + 1) (Pi.mulSingle (Fin.last k) ζ))) : NormConcl p A D := by
  classical
  haveI := Fact.mk hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hζp : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζo
    exact hp.one_lt.ne hζo
  have hζ2 : ζ * ζ ≠ 1 := by
    intro h
    have h2 : ζ ^ 2 = 1 := by rw [sq]; exact h
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hζo] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  set Ω := LargeEvenOmega (LargeEvenQMinus (k + 1) b c) with hΩ
  set a := dgHomM K (k + 1) (Pi.mulSingle (Fin.last k) ζ) with ha
  have ha' : a = TauCeti.diagGL (Sum.elim (pairedUnits (Pi.mulSingle (Fin.last k) ζ)) 1) :=
    dgHomM_apply _
  set e := minusSplit k with he
  have hQ := largeEvenQMinus_split (K := K) k b c
  have hPT : IsPairTorus e (Sum.elim (pairedUnits (Pi.mulSingle (Fin.last k) ζ)) 1) ζ :=
    isPairTorus_minus hζ2
  set Y : Subgroup (GL (LargeEvenMinusIdx (k + 1)) K) :=
    (LargeEvenOmega (LargeEvenQMinus k b c)).map (embHom e) with hY
  have hYΩ : Y ≤ Ω := map_embHom_omega_le hQ
  have hYc : ∀ y ∈ Y, y * a = a * y := by
    rintro _ ⟨h, -, rfl⟩
    rw [ha']
    exact Subgroup.mem_centralizer_singleton_iff.mp (hPT.embHom_mem_centralizer h)
  have hcomm : ∀ g ∈ Ω, g * a = a * g → ∀ g' ∈ Ω, g' * a = a * g' →
      g * g' * g⁻¹ * g'⁻¹ ∈ Y := fun g hg hgc g' hg' hg'c =>
    hPT.commutator_mem_map_embHom_omega hQ
      (Subgroup.mem_centralizer_singleton_iff.mpr (by rw [← ha']; exact hgc))
      (Subgroup.mem_centralizer_singleton_iff.mpr (by rw [← ha']; exact hg'c))
      (omega_le_orth _ hg) (omega_le_orth _ hg')
  have hYq : CFSG.IsQuasisimple Y :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((LargeEvenOmega (LargeEvenQMinus k b c)).equivMapOfInjective _ (embHom_injective e))
      (isQuasisimple_omegaMinus hk hirr)
  have hDY : D ≤ Y := by
    have hperf : ⁅D, D⁆ = D := Subgroup.isPerfect_iff.1 hE.D_qs.1
    rw [← hperf]
    refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    rw [commutatorElement_def]
    exact hcomm x (hE.D_le hx) (hE.D_cent x hx) y (hE.D_le hy) (hE.D_cent y hy)
  have hDeq : D = Y := StdSubRestThree.eq_of_le_of_quasisimple hDY
    (fun b hb d hd => hE.D_norm b (hYΩ hb) (hYc b hb) d hd) hYq hE.D_qs
  set i₀ : Fin (k + 1) := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin (k + 1) := ⟨1, by omega⟩ with hi₁
  have h01 : i₁ ≠ i₀ := by simp [hi₀, hi₁, Fin.ext_iff]
  have hi₀l : i₀ ≠ Fin.last k := by simp [hi₀, Fin.ext_iff]; omega
  have hi₁l : i₁ ≠ Fin.last k := by simp [hi₁, Fin.ext_iff]; omega
  set X : Multiplicative K →* GL (LargeEvenMinusIdx (k + 1)) K :=
    blockInl.comp (siegelHom i₀ i₁) with hX
  have hXconj : ∀ (w : Fin (k + 1) → Kˣ) (c' : Multiplicative K),
      dgHomM K (k + 1) w * X c' * (dgHomM K (k + 1) w)⁻¹ =
        X (Multiplicative.ofAdd
          (((w i₀ : Kˣ) : K) * ((w i₁ : Kˣ) : K) * Multiplicative.toAdd c')) := by
    intro w c'
    change blockInl (dgHom K (k + 1) w) * blockInl (siegelHom i₀ i₁ c') *
      (blockInl (dgHom K (k + 1) w))⁻¹ = blockInl (siegelHom i₀ i₁ _)
    rw [← map_inv, ← map_mul, ← map_mul, dgHom_apply, siegelHom_apply, siegelHom_apply,
      diagGL_pairedUnits_conj_siegelGL]
    simp only [toAdd_ofAdd]
  have hXmem : ∀ c', X c' ∈ Ω := fun c' =>
    blockInl_mem_omegaMinus b c (siegelGL_mem_omegaPlus hζp hζ1 h01 _)
  have hXc : ∀ c', X c' * a = a * X c' := by
    intro c'
    have h1 := hXconj (Pi.mulSingle (Fin.last k) ζ) c'
    rw [Pi.mulSingle_eq_of_ne hi₀l, Pi.mulSingle_eq_of_ne hi₁l] at h1
    simp only [Units.val_one, one_mul, ofAdd_toAdd] at h1
    rw [← ha] at h1
    calc X c' * a = (a * X c' * a⁻¹) * a := by rw [h1]
      _ = a * X c' := by group
  have hXinj : Function.Injective X :=
    blockInl_injective.comp (fun x y h => by
      have h' := siegelGL_injective h01 (by simpa [siegelHom_apply] using h)
      exact Multiplicative.toAdd.injective h')
  set w₀ : Fin (k + 1) → Kˣ := Pi.mulSingle i₀ ζ with hw₀
  have hw₀p : ∀ j, w₀ j ^ p = 1 := by
    intro j
    by_cases hj : j = i₀
    · subst hj
      rw [hw₀, Pi.mulSingle_eq_same]
      exact hζp
    · rw [hw₀, Pi.mulSingle_eq_of_ne hj, one_pow]
  have ht₀A : dgHomM K (k + 1) w₀ ∈ A := hT.2 w₀ hw₀p
  have ht₀c : dgHomM K (k + 1) w₀ * a = a * dgHomM K (k + 1) w₀ := by
    rw [ha, ← map_mul, ← map_mul, mul_comm]
  have hζK : (ζ : K) - 1 ≠ 0 := sub_ne_zero.mpr fun h => hζ1 (Units.ext h)
  have hXY : ∀ y : K, X (Multiplicative.ofAdd y) ∈ Y := by
    intro y
    set x : K := y / ((ζ : K) - 1) with hx
    have h1 := hcomm _ (hE.A_le ht₀A) ht₀c (X (Multiplicative.ofAdd x)) (hXmem _) (hXc _)
    rw [hXconj, hw₀, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h01, ← map_inv, ← map_mul]
      at h1
    convert h1 using 2
    simp only [toAdd_ofAdd, Units.val_one, mul_one]
    rw [← ofAdd_neg, ← ofAdd_add]
    congr 1
    rw [hx]
    field_simp
    ring
  set U : Subgroup (GL (LargeEvenMinusIdx (k + 1)) K) := X.range with hU
  have hAU : ∀ s ∈ A, ∀ u ∈ U, s * u * s⁻¹ ∈ U := by
    intro s hs u hu
    obtain ⟨w, -, rfl⟩ := hT.1 s hs
    obtain ⟨c', rfl⟩ := hu
    rw [hXconj]
    exact ⟨_, rfl⟩
  set t : GL (LargeEvenMinusIdx (k + 1)) K := dgHomM K (k + 1) w₀ with ht
  have htU : ∀ h ∈ U, t * h * t⁻¹ ∈ U := fun h hh => hAU t ht₀A h hh
  have htU' : ∀ h ∈ U, t⁻¹ * h * t ∈ U := fun h hh => by
    simpa using hAU t⁻¹ (A.inv_mem ht₀A) h hh
  have htY : t ∈ Y := by
    set f' : Fin (k + 1) → Multiplicative (ZMod p) := Pi.mulSingle i₀ (Multiplicative.ofAdd 1)
      with hf'
    set u : Fin (k + 1) → Kˣ := fun j => zmodPowHom hζp (f' j) with hu
    have hu0 : u = w₀ := by
      funext j
      by_cases hj : j = i₀
      · subst hj
        have h := zmodPowHom_mulSingle_self (K := K) hζp i₀
        simp only [hu, hf', hw₀, Pi.mulSingle_eq_same] at h ⊢
        exact h
      · simp only [hu, hf', hw₀, Pi.mulSingle_eq_of_ne hj, map_one]
    have hlast : u (Fin.last k) = 1 := by
      rw [hu0, hw₀, Pi.mulSingle_eq_of_ne (Ne.symm hi₀l)]
    have h1 := embHom_minusSplit_diag u hlast
    have h2 : t = TauCeti.diagGL (Sum.elim (pairedUnits u) 1) := by
      rw [ht, ← hu0]
      exact dgHomM_apply _
    rw [h2, ← h1]
    refine ⟨TauCeti.diagGL (Sum.elim (pairedUnits fun j => u (Fin.castSucc j)) 1), ?_, rfl⟩
    rw [← blockInl_diagGL]
    exact blockInl_mem_omegaMinus b c (spTorusGL_mem_omegaPlus (K := K) (m := k) hζp
      (hp.odd_of_ne_two hp2) (fun j => f' (Fin.castSucc j)))
  refine NormConcl.intro U (hDeq ▸ ?_) ?_ ?_ hAU t (hDeq ▸ htY) ?_ ?_ ?_
    (X (Multiplicative.ofAdd 1)) (hDeq ▸ hXY 1) ?_
  · rintro _ ⟨c', rfl⟩
    have := hXY (Multiplicative.toAdd c')
    rwa [ofAdd_toAdd] at this
  · intro hbot
    have h1 : X (Multiplicative.ofAdd (1 : K)) ∈ U := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : Multiplicative.ofAdd (1 : K) = 1 := hXinj (by rw [h1, map_one])
    exact one_ne_zero (ofAdd_eq_one.mp h2)
  · intro g
    obtain ⟨c', hc'⟩ := g.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, ← hc', ← map_pow]
    have : c' ^ 2 = 1 := by
      rw [← ofAdd_toAdd c', ← ofAdd_nsmul, two_nsmul, CharTwo.add_self_eq_zero, ofAdd_zero]
    rw [this, map_one]
    rfl
  · rw [ht, ← map_pow]
    have : w₀ ^ p = 1 := funext fun j => hw₀p j
    rw [this, map_one]
  · intro s hs
    obtain ⟨w, -, rfl⟩ := hT.1 s hs
    rw [ht, ← map_mul, ← map_mul, mul_comm]
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => htU h hh, fun hh => ?_⟩
    have h5 := htU' _ hh
    have e : t⁻¹ * (t * h * t⁻¹) * t = h := by group
    rwa [e] at h5
  · intro hcomm'
    have h1 : t * X (Multiplicative.ofAdd 1) * t⁻¹ = X (Multiplicative.ofAdd 1) := by
      rw [hcomm', mul_inv_cancel_right]
    rw [ht, hXconj, hw₀, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h01] at h1
    have h2 := Multiplicative.ofAdd.injective (hXinj h1)
    apply hζ1
    exact Units.ext (by simpa using h2)

theorem minus_reduce_norm {p : ℕ} {b c : K} {A D : Subgroup (GL (LargeEvenMinusIdx m) K)}
    {a : GL (LargeEvenMinusIdx m) K}
    (hE : EndData p (LargeEvenOmega (LargeEvenQMinus m b c)) A D a) (hT : IsFullTorusM p A)
    (s : GL (LargeEvenMinusIdx m) K) (hs : s ∈ LargeEvenOrthGroup (LargeEvenQMinus m b c))
    (τ : (Fin m → Kˣ) → Fin m → Kˣ) (hτ : ∀ u, s * dgHomM K m u * s⁻¹ = dgHomM K m (τ u))
    (hτp : ∀ u : Fin m → Kˣ, (∀ k, u k ^ p = 1) → ∀ k, τ u k ^ p = 1)
    (hτs : ∀ u' : Fin m → Kˣ, (∀ k, u' k ^ p = 1) → ∃ u : Fin m → Kˣ,
      (∀ k, u k ^ p = 1) ∧ τ u = u')
    (h : ∀ (A' D' : Subgroup (GL (LargeEvenMinusIdx m) K)),
      EndData p (LargeEvenOmega (LargeEvenQMinus m b c)) A' D' (s * a * s⁻¹) →
        IsFullTorusM p A' → NormConcl p A' D') : NormConcl p A D := by
  have hφ := map_conj_omega hs
  have h1 : EndData p (LargeEvenOmega (LargeEvenQMinus m b c))
      (A.map (MulAut.conj s).toMonoidHom) (D.map (MulAut.conj s).toMonoidHom) (s * a * s⁻¹) := by
    have := hE.map (MulAut.conj s) hφ
    simpa only [MulAut.conj_apply] using this
  exact NormConcl.of_map (MulAut.conj s) (h _ _ h1 (hT.map_conj s τ hτ hτp hτs))

theorem minus_toral_norm [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ}
    (hm : 3 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {A D : Subgroup (GL (LargeEvenMinusIdx m) K)} {a : GL (LargeEvenMinusIdx m) K}
    (hE : EndData p (LargeEvenOmega (LargeEvenQMinus m b c)) A D a) (hT : IsFullTorusM p A) :
    NormConcl p A D := by
  classical
  haveI := Fact.mk hp
  obtain ⟨α, hα, rfl⟩ := hT.1 a hE.a_mem
  rcases minus_dichotomy hp hT hα hE with ⟨i₀, hi₀, hrest⟩ | hall
  ·
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    set σ : Equiv.Perm (Fin (k + 1)) := Equiv.swap i₀ (Fin.last k) with hσ
    have hord : orderOf (α i₀) = p := orderOf_eq_prime (hα i₀) hi₀
    refine minus_reduce_norm hE hT
      (blockInl (TauCeti.permutationGL (k := K) (Equiv.Perm.sumCongr σ σ)))
      (blockInl_mem_orth (sumCongr_mem_orthPlus σ)) (fun u k => u (σ⁻¹ k))
      (conj_dgHomM_perm σ) (fun u hu k => hu _)
      (fun u' hu' => ⟨fun k => u' (σ k), fun k => hu' _, ?_⟩) ?_
    · funext j
      simp
    · intro A' D' hE' hT'
      have e : (fun k => α (σ⁻¹ k)) = Pi.mulSingle (Fin.last k) (α i₀) := by
        funext j
        by_cases hj : j = Fin.last k
        · subst hj
          simp [hσ]
        · rw [Pi.mulSingle_eq_of_ne hj]
          apply hrest
          intro h
          apply hj
          have h1 : σ (σ⁻¹ j) = j := σ.apply_symm_apply j
          rw [h, hσ, Equiv.swap_apply_left] at h1
          exact h1.symm
      rw [conj_dgHomM_perm, e] at hE'
      exact minus_alpha_three hp hp2 (by omega) hirr hord hT' hE'
  ·
    set ν := α ⟨0, by omega⟩ with hν
    have hν1 : ν ≠ 1 := hall _
    have hord : orderOf ν = p := orderOf_eq_prime (hα _) hν1
    have hcls : ∀ k, α k = ν ∨ α k = ν⁻¹ := fun k =>
      minus_two_class hp hT hα hE (hall ⟨0, by omega⟩) (hall k)
    set F : Fin m → Prop := fun k => α k = ν⁻¹ with hF
    refine minus_reduce_norm hE hT (blockInl (TauCeti.permutationGL (k := K) (swapOn F)))
      (blockInl_mem_orth (swapOn_mem_orth F)) (fun u k => if F k then (u k)⁻¹ else u k)
      (conj_dgHomM_swapOn F)
      (fun u hu k => by
        by_cases h : F k
        · simp only [if_pos h, inv_pow, hu k, inv_one]
        · simp only [if_neg h, hu k])
      (fun u' hu' => ⟨fun k => if F k then (u' k)⁻¹ else u' k, fun k => by
        by_cases h : F k
        · simp only [if_pos h, inv_pow, hu' k, inv_one]
        · simp only [if_neg h, hu' k], ?_⟩) ?_
    · funext k
      by_cases h : F k <;> simp [h]
    · intro A' D' hE' hT'
      have e : (fun k => if F k then (α k)⁻¹ else α k) = fun _ => ν := by
        funext k
        by_cases h : F k
        · simp only [if_pos h]
          rw [show α k = ν⁻¹ from h, inv_inv]
        · simp only [if_neg h]
          exact (hcls k).resolve_right h
      rw [conj_dgHomM_swapOn, e] at hE'
      exact minus_beta_three hp hp2 hm hord hT' hE'

theorem minus_norm_big [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) {m : ℕ} (hm : 3 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {A D : Subgroup (GL (LargeEvenMinusIdx m) K)}
    {a : GL (LargeEvenMinusIdx m) K}
    (hE : EndData p (LargeEvenOmega (LargeEvenQMinus m b c)) A D a) (hr : p ^ m ≤ Nat.card A) :
    NormConcl p A D := by
  haveI := Fact.mk hp
  obtain ⟨ζ, hζo, -, -, -⟩ := exists_zeta (K := K) hp hp2 hpK
  obtain ⟨g, hgO, χ, hχ, hsurj⟩ := exists_orth_conj_minus hp2 hζo hirr
    (hE.A_le.trans (omega_le_orth _)) hE.A_elem hr
  refine NormConcl.of_map (MulAut.conj g) (minus_toral_norm hp hp2 hm hirr
    (hE.map (MulAut.conj g) (map_conj_omega hgO)) ?_)
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨fun k => χ k ⟨x, hx⟩, fun k => ?_, ?_⟩
    · rw [← map_pow]
      have : (⟨x, hx⟩ : A) ^ p = 1 := Subtype.ext (hE.A_elem.2 x hx)
      rw [this, map_one]
    · have := hχ ⟨x, hx⟩
      change blockInl (dgHom K m _) = _
      rw [dgHom_apply]
      simpa [MulAut.conj_apply] using this.symm
  · intro u hu
    obtain ⟨x, hx⟩ := hsurj u hu
    refine ⟨x, x.2, ?_⟩
    have := hχ x
    change _ = blockInl (dgHom K m u)
    rw [dgHom_apply]
    have hu' : (fun k => χ k x) = u := funext hx
    rw [hu'] at this
    simpa [MulAut.conj_apply] using this

end MinusToral

theorem minusSplitInput_holds : MinusSplitInput := by
  intro K _ _ n m p b c hK hm hp hpn hirr
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have : 1 < Nat.card K := Finite.one_lt_card
      rw [hK, h0, pow_zero] at this
      omega
    · exact h0
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hK
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one' hn hpn
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  set e := projMkEquiv (scalars_subgroupOf_omegaMinus_eq_bot (K := K) (m := m) b c) with he
  set f : OrthRest.RMinus K m b c →* GL (LargeEvenMinusIdx m) K :=
    (LargeEvenOmega (LargeEvenQMinus m b c)).subtype.comp e.symm.toMonoidHom with hf
  have hfinj : Function.Injective f := fun x y h =>
    e.symm.injective (Subtype.ext h)
  have hfrange : f.range = LargeEvenOmega (LargeEvenQMinus m b c) := by
    ext x
    constructor
    · rintro ⟨r, rfl⟩
      exact (e.symm r).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [hf]⟩
  exact eltNormSmall_of_ambient' (LargeEvenOmega (LargeEvenQMinus m b c)) f hfinj hfrange
    fun A D a hE hr => Or.inr (minus_norm_big hp hp2 hpK hm hirr hE hr)

end SmallOrth

end CFSG.StandardType

end
