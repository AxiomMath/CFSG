module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthInDiag
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix TableBSymp TableBOrth

open scoped commutatorElement

namespace SmallOrth

section PlusToral

variable {K : Type} [Field K] {m : ℕ}

@[expose] noncomputable def dgHom (K : Type) [Field K] (m : ℕ) :
    (Fin m → Kˣ) →* GL (Fin m ⊕ Fin m) K :=
  TauCeti.diagGL.comp pairedHom

theorem dgHom_apply (u : Fin m → Kˣ) : dgHom K m u = TauCeti.diagGL (pairedUnits u) := rfl

theorem coe_dgHom (u : Fin m → Kˣ) :
    ((dgHom K m u : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      Matrix.fromBlocks (Matrix.diagonal fun k => ((u k : Kˣ) : K)) 0 0
        (Matrix.diagonal fun k => (((u k)⁻¹ : Kˣ) : K)) := by
  rw [dgHom_apply, TauCeti.diagGL_coe, Matrix.fromBlocks_diagonal]
  congr 1
  funext y
  rcases y with k | k <;> rfl

theorem dgHom_injective : Function.Injective (dgHom K m) := by
  intro u v h
  have h1 : pairedUnits u = pairedUnits v := TauCeti.diagGL_injective h
  funext k
  have := congrFun h1 (Sum.inl k)
  simpa [pairedUnits] using this

def IsFullTorus (p : ℕ) (A : Subgroup (GL (Fin m ⊕ Fin m) K)) : Prop :=
  (∀ x ∈ A, ∃ u : Fin m → Kˣ, (∀ k, u k ^ p = 1) ∧ dgHom K m u = x) ∧
    ∀ u : Fin m → Kˣ, (∀ k, u k ^ p = 1) → dgHom K m u ∈ A

theorem zpow_eq_self_of_order {p : ℕ} (hp : p.Prime) {u v : Kˣ} (hu : u ^ p = 1) (hu1 : u ≠ 1)
    (hv : v ^ p = 1) (hv1 : v ≠ 1) {s : ℤ} (h : u ^ s = u) : v ^ s = v := by
  haveI := Fact.mk hp
  have hou : orderOf u = p := orderOf_eq_prime hu hu1
  have hov : orderOf v = p := orderOf_eq_prime hv hv1
  have h1 : u ^ s = u ^ (1 : ℤ) := by rw [zpow_one]; exact h
  rw [zpow_eq_zpow_iff_modEq, hou] at h1
  have h2 : v ^ s = v ^ (1 : ℤ) := by rw [zpow_eq_zpow_iff_modEq, hov]; exact h1
  rwa [zpow_one] at h2

theorem exists_zpow_of_mem_zpowers {α w : Fin m → Kˣ}
    (h : dgHom K m w ∈ Subgroup.zpowers (dgHom K m α)) : ∃ s : ℤ, ∀ k, w k = α k ^ s := by
  obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp h
  have : α ^ s = w := dgHom_injective (by rw [map_zpow]; exact hs)
  exact ⟨s, fun k => by rw [← this]; rfl⟩

theorem pairedUnits_map (F : Kˣ → Kˣ) (hF : ∀ t, F t⁻¹ = (F t)⁻¹) (u : Fin m → Kˣ) :
    pairedUnits (fun k => F (u k)) = fun y => F (pairedUnits u y) := by
  funext y
  rcases y with k | k
  · rfl
  · simp [pairedUnits, hF]

theorem plus_two_class {p : ℕ} (hp : p.Prime) {Ω A D : Subgroup (GL (Fin m ⊕ Fin m) K)}
    {α : Fin m → Kˣ} (hT : IsFullTorus p A) (hα : ∀ k, α k ^ p = 1)
    (hE : EndData p Ω A D (dgHom K m α)) {i j : Fin m} (hi : α i ≠ 1) (hj : α j ≠ 1) :
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
  have hFp : ∀ t : Kˣ, t ^ p = 1 → F t ^ p = 1 := by
    intro t ht
    by_cases h : t = ν ∨ t = ν⁻¹
    · simp only [hF, if_pos h, ht]
    · simp only [hF, if_neg h, one_pow]
  set w : Fin m → Kˣ := fun k => F (α k) with hw
  have hwp : ∀ k, w k ^ p = 1 := fun k => hFp _ (hα k)
  have hxA : dgHom K m w ∈ A := hT.2 w hwp
  have hcomm : ∀ d ∈ D, dgHom K m w * d = d * dgHom K m w := by
    intro d hd
    have hda := hE.D_cent d hd
    have hw' : pairedUnits w = fun y => F (pairedUnits α y) := pairedUnits_map F hFinv α
    refine commute_of_function (δ := pairedUnits α) (ε := pairedUnits w) (fun y z hyz => ?_) hda
    rw [hw']
    show F (pairedUnits α y) = F (pairedUnits α z)
    rw [hyz]
  obtain ⟨s, hs⟩ := exists_zpow_of_mem_zpowers (hE.A_cent _ hxA hcomm)
  have hFν : F ν = ν := by simp [hF]
  have hFj : F (α j) = 1 := by
    have : ¬ (α j = ν ∨ α j = ν⁻¹) := fun h => h.elim hj1 hj2
    simp only [hF, if_neg this]
  have hwi : w i = ν := hFν
  have hwj : w j = 1 := hFj
  have h1 : ν ^ s = ν := by rw [← hs i, hwi]
  have h2 : α j ^ s = α j :=
    zpow_eq_self_of_order hp (hα i) hi (hα j) hj h1
  have h3 : α j = 1 := by rw [← h2, ← hs j, hwj]
  exact hj h3

theorem plus_dichotomy {p : ℕ} (hp : p.Prime) {Ω A D : Subgroup (GL (Fin m ⊕ Fin m) K)}
    {α : Fin m → Kˣ} (hT : IsFullTorus p A) (hα : ∀ k, α k ^ p = 1)
    (hE : EndData p Ω A D (dgHom K m α)) :
    (∃ i₀, α i₀ ≠ 1 ∧ ∀ k, k ≠ i₀ → α k = 1) ∨ ∀ k, α k ≠ 1 := by
  classical
  have hex : ∃ i₀, α i₀ ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hE.a_ne
    have : α = 1 := funext hall
    rw [this, map_one]
  obtain ⟨i₀, hi₀⟩ := hex
  have ha : dgHom K m α = TauCeti.diagGL (pairedUnits α) := rfl
  set δ : Fin m ⊕ Fin m → Kˣ := pairedUnits α with hδ
  set C : Subgroup (GL (Fin m ⊕ Fin m) K) := Ω ⊓ Subgroup.centralizer {dgHom K m α} with hC
  have hDC : D ≤ C := fun d hd =>
    ⟨hE.D_le hd, Subgroup.mem_centralizer_singleton_iff.mpr (hE.D_cent d hd)⟩
  have hBC : fixStar Ω δ ≤ C := fun g hg =>
    ⟨hg.1, Subgroup.mem_centralizer_singleton_iff.mpr hg.2.1⟩
  have hDn : ∀ c ∈ C, ∀ d ∈ D, c * d * c⁻¹ ∈ D := fun c hc d hd =>
    hE.D_norm c hc.1 (Subgroup.mem_centralizer_singleton_iff.mp hc.2) d hd
  have hBn : ∀ c ∈ C, ∀ b ∈ fixStar Ω δ, c * b * c⁻¹ ∈ fixStar Ω δ := fun c hc b hb =>
    fixStar_normal hc.1 (Subgroup.mem_centralizer_singleton_iff.mp hc.2) hb
  have hi₀p := hα i₀
  rcases commute_or_le hDC hBC hDn hBn hE.D_qs with hle | hcomm
  ·
    left
    refine ⟨i₀, hi₀, fun j hj => ?_⟩
    by_contra hj1
    set x : GL (Fin m ⊕ Fin m) K := dgHom K m (Pi.mulSingle i₀ (α i₀)) with hx
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
      refine commute_of_fixStar (δ := δ) (ε := pairedUnits (Pi.mulSingle i₀ (α i₀))) ?_ (hle hd)
      intro y hy
      rcases y with k | k
      · have hk : α k = 1 := hy
        have hki : k ≠ i₀ := fun h => hi₀ (h ▸ hk)
        simp [pairedUnits, Pi.mulSingle_eq_of_ne hki]
      · have hk : (α k)⁻¹ = 1 := hy
        have hk' : α k = 1 := inv_eq_one.mp hk
        have hki : k ≠ i₀ := fun h => hi₀ (h ▸ hk')
        simp [pairedUnits, Pi.mulSingle_eq_of_ne hki]
    obtain ⟨s, hs⟩ := exists_zpow_of_mem_zpowers (hE.A_cent x hxA hxD)
    have h1 : α i₀ ^ s = α i₀ := by rw [← hs i₀, Pi.mulSingle_eq_same]
    have h2 : α j ^ s = α j := zpow_eq_self_of_order hp hi₀p hi₀ (hα j) hj1 h1
    have h3 : α j = 1 := by
      rw [← h2, ← hs j, Pi.mulSingle_eq_of_ne hj]
    exact hj1 h3
  ·
    right
    intro k hk
    set x : GL (Fin m ⊕ Fin m) K := dgHom K m (Pi.mulSingle k (α i₀)) with hx
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
      · refine diag_mul_pStar (δ := δ) (ε := pairedUnits (Pi.mulSingle k (α i₀))) ?_
        intro y hy
        rcases y with k' | k'
        · have hk' : k' ≠ k := fun h => hy (h ▸ hk)
          simp [pairedUnits, Pi.mulSingle_eq_of_ne hk']
        · have hk' : k' ≠ k := fun h => hy (by simp [hδ, pairedUnits, h, hk])
          simp [pairedUnits, Pi.mulSingle_eq_of_ne hk']
    have hxD : ∀ d ∈ D, x * d = d * x := fun d hd => (hcomm d hd x hxB).symm
    obtain ⟨s, hs⟩ := exists_zpow_of_mem_zpowers (hE.A_cent x hxA hxD)
    have h1 : α i₀ = 1 := by
      have := hs k
      rwa [Pi.mulSingle_eq_same, hk, _root_.one_zpow] at this
    exact hi₀ h1

theorem embHom_plusSplit_diag {k : ℕ} (u : Fin (k + 1) → Kˣ) (hu : u (Fin.last k) = 1) :
    embHom (plusSplit k) (TauCeti.diagGL (pairedUnits fun j => u (Fin.castSucc j))) =
      TauCeti.diagGL (pairedUnits u) := by
  apply Units.ext
  apply (Matrix.reindex (plusSplit k) (plusSplit k)).injective
  have h1 : (1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) = Matrix.diagonal (fun _ => 1) :=
    Matrix.diagonal_one.symm
  rw [reindex_embHom, TauCeti.diagGL_coe, TauCeti.diagGL_coe, Matrix.reindex_apply,
    Matrix.submatrix_diagonal_equiv, h1, Matrix.fromBlocks_diagonal]
  congr 1
  funext z
  rcases z with x | a
  · rcases x with x | x
    · simp [plusSplit_symm_inl_inl, pairedUnits]
    · simp [plusSplit_symm_inl_inr, pairedUnits]
  · rcases a with a | a
    · simp [plusSplit_symm_inr_inl, pairedUnits, hu]
    · simp [plusSplit_symm_inr_inr, pairedUnits, hu]

@[expose] noncomputable def extThree {m p : ℕ} (f : Fin 3 → Multiplicative (ZMod p)) :
    Fin m → Multiplicative (ZMod p) :=
  fun j => if h : j.val < 3 then f ⟨j.val, h⟩ else 1

theorem extThree_injective {m p : ℕ} (hm : 3 ≤ m) :
    Function.Injective (extThree (m := m) (p := p)) := by
  intro f g h
  funext j
  have := congrFun h ⟨j.val, by omega⟩
  simpa [extThree, j.2] using this

theorem plus_final_alpha [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ} (hk : 3 ≤ k)
    {ζ : Kˣ} (hζo : orderOf ζ = p) {A D : Subgroup (GL (Fin (k + 1) ⊕ Fin (k + 1)) K)}
    (hT : IsFullTorus p A)
    (hE : EndData p (LargeEvenOmega (LargeEvenQPlus K (k + 1))) A D
      (dgHom K (k + 1) (Pi.mulSingle (Fin.last k) ζ))) : BigConcl p A D := by
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
  set Ω := LargeEvenOmega (LargeEvenQPlus K (k + 1)) with hΩ
  set a := dgHom K (k + 1) (Pi.mulSingle (Fin.last k) ζ) with ha
  set e := plusSplit k with he
  have hQ := largeEvenQPlus_split (K := K) k
  have hPT : IsPairTorus e (pairedUnits (Pi.mulSingle (Fin.last k) ζ)) ζ := isPairTorus_plus hζ2
  set Y : Subgroup (GL (Fin (k + 1) ⊕ Fin (k + 1)) K) :=
    (LargeEvenOmega (LargeEvenQPlus K k)).map (embHom e) with hY
  have hYΩ : Y ≤ Ω := map_embHom_omega_le hQ
  have hYc : ∀ y ∈ Y, y * a = a * y := by
    rintro _ ⟨h, -, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hPT.embHom_mem_centralizer h)
  have hcomm : ∀ g ∈ Ω, g * a = a * g → ∀ g' ∈ Ω, g' * a = a * g' →
      g * g' * g⁻¹ * g'⁻¹ ∈ Y := fun g hg hgc g' hg' hg'c =>
    hPT.commutator_mem_map_embHom_omega hQ (Subgroup.mem_centralizer_singleton_iff.mpr hgc)
      (Subgroup.mem_centralizer_singleton_iff.mpr hg'c) (omega_le_orth _ hg) (omega_le_orth _ hg')
  have hYq : CFSG.IsQuasisimple Y :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((LargeEvenOmega (LargeEvenQPlus K k)).equivMapOfInjective _ (embHom_injective e))
      (isQuasisimple_omegaPlus hk)
  have hDY : D ≤ Y := by
    have hperf : ⁅D, D⁆ = D := Subgroup.isPerfect_iff.1 hE.D_qs.1
    rw [← hperf]
    refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    rw [commutatorElement_def]
    exact hcomm x (hE.D_le hx) (hE.D_cent x hx) y (hE.D_le hy) (hE.D_cent y hy)
  have hDeq : D = Y := StdSubRestThree.eq_of_le_of_quasisimple hDY
    (fun b hb d hd => hE.D_norm b (hYΩ hb) (hYc b hb) d hd) hYq hE.D_qs
  let g : (Fin 3 → Multiplicative (ZMod p)) → GL (Fin (k + 1) ⊕ Fin (k + 1)) K :=
    fun f => spTorusGL hζp (extThree f)
  have hgA : ∀ f, g f ∈ A := fun f => by
    have := hT.2 (fun j => zmodPowHom hζp (extThree f j)) (fun j => by
      rw [← map_pow]
      have : extThree f j ^ p = 1 := by
        have h1 : (extThree f ^ p) j = 1 := by rw [pow_card_eq_one_zmod]; rfl
        exact h1
      rw [this, map_one])
    exact this
  have hgY : ∀ f, g f ∈ Y := fun f => by
    set u : Fin (k + 1) → Kˣ := fun j => zmodPowHom hζp (extThree f j) with hu
    have hlast : u (Fin.last k) = 1 := by
      have : ¬ k < 3 := by omega
      simp [hu, extThree, this]
    have h1 := embHom_plusSplit_diag u hlast
    have h2 : g f = TauCeti.diagGL (pairedUnits u) := rfl
    rw [h2, ← h1]
    refine ⟨TauCeti.diagGL (pairedUnits fun j => u (Fin.castSucc j)), ?_, rfl⟩
    exact spTorusGL_mem_omegaPlus (K := K) (m := k) hζp (hp.odd_of_ne_two hp2)
      (fun j => extThree f (Fin.castSucc j))
  have hginj : Function.Injective g := by
    intro f f' h
    have h1 : (fun j => zmodPowHom hζp (extThree f j)) = fun j => zmodPowHom hζp (extThree f' j) :=
      dgHom_injective h
    have hzinj : Function.Injective (zmodPowHom hζp : Multiplicative (ZMod p) →* Kˣ) :=
      (injective_iff_map_eq_one _).2 fun a ha => (zmodPowHom_eq_one_iff hζp hζo).1 ha
    exact extThree_injective (by omega) (funext fun j => hzinj (congrFun h1 j))
  exact BigConcl.intro (A ⊓ D) (isElemAbelian_of_le hE.A_elem inf_le_left) inf_le_right
    inf_le_left (three_pow_le_card (A ⊓ D) g hginj fun f => ⟨hgA f, hDeq ▸ hgY f⟩)

@[expose] noncomputable def leviUnit (K : Type) [Field K] (m : ℕ) (h : GL (Fin m) K) :
    GL (Fin m ⊕ Fin m) K where
  val := Matrix.fromBlocks (h : Matrix (Fin m) (Fin m) K) 0 0
    (((h⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))ᵀ
  inv := Matrix.fromBlocks ((h⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) 0 0
    (h : Matrix (Fin m) (Fin m) K)ᵀ
  val_inv := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.fromBlocks_one]
  inv_val := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.fromBlocks_one]

@[expose] noncomputable def leviHom (K : Type) [Field K] (m : ℕ) :
    GL (Fin m) K →* GL (Fin m ⊕ Fin m) K where
  toFun := leviUnit K m
  map_one' := by
    apply Units.ext
    simp only [leviUnit, inv_one, Units.val_one, Matrix.transpose_one, Matrix.fromBlocks_one]
  map_mul' h h' := by
    apply Units.ext
    simp only [leviUnit, _root_.mul_inv_rev, Units.val_mul, Matrix.fromBlocks_multiply,
      Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.transpose_mul]

theorem coe_leviHom (h : GL (Fin m) K) :
    ((leviHom K m h : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      Matrix.fromBlocks (h : Matrix (Fin m) (Fin m) K) 0 0
        (((h⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))ᵀ := rfl

theorem leviHom_injective : Function.Injective (leviHom K m) := by
  intro h h' hh
  apply Units.ext
  have := congrArg (fun g : GL (Fin m ⊕ Fin m) K =>
    (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).toBlocks₁₁) hh
  simpa [coe_leviHom] using this

theorem dot_leviHom (h : GL (Fin m) K) (x y : Fin m → K) :
    ((h : Matrix (Fin m) (Fin m) K) *ᵥ x) ⬝ᵥ
      ((((h⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)ᵀ) *ᵥ y) = x ⬝ᵥ y := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, Matrix.vecMul_vecMul,
    Units.inv_mul, Matrix.vecMul_one, dotProduct_comm]

theorem leviHom_mem_orth (h : GL (Fin m) K) :
    leviHom K m h ∈ LargeEvenOrthGroup (LargeEvenQPlus K m) := by
  refine mem_orthGroup_of_isometry fun v => ?_
  obtain ⟨x, y, rfl⟩ : ∃ x y : Fin m → K, v = Sum.elim x y :=
    ⟨v ∘ Sum.inl, v ∘ Sum.inr, (Sum.elim_comp_inl_inr v).symm⟩
  rw [coe_leviHom, Matrix.fromBlocks_mulVec, largeEvenQPlus_eq, largeEvenQPlus_eq]
  simp only [Matrix.zero_mulVec, add_zero, zero_add, Function.comp_def, Sum.elim_inl,
    Sum.elim_inr]
  exact dot_leviHom h x y

theorem leviHom_commute (ν : Kˣ) (h : GL (Fin m) K) :
    leviHom K m h * dgHom K m (fun _ => ν) = dgHom K m (fun _ => ν) * leviHom K m h := by
  apply Units.ext
  have hd := coe_dgHom (K := K) (m := m) (fun _ => ν)
  rw [Units.val_mul, Units.val_mul, hd, coe_leviHom, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  congr 1
  · ext i j
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]
  · ext i j
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem exists_leviHom_eq {ν : Kˣ} (hν : ν * ν ≠ 1) {g : GL (Fin m ⊕ Fin m) K}
    (hgc : g * dgHom K m (fun _ => ν) = dgHom K m (fun _ => ν) * g)
    (hgO : g ∈ LargeEvenOrthGroup (LargeEvenQPlus K m)) :
    ∃ h : GL (Fin m) K, leviHom K m h = g := by
  rw [dgHom_apply] at hgc
  have hm := commute_diagGL_iff.mp hgc
  have hne : ν ≠ ν⁻¹ := fun h => hν (by nth_rewrite 2 [h]; exact mul_inv_cancel ν)
  have hdiff : ((ν : Kˣ) : K) ≠ ((ν⁻¹ : Kˣ) : K) := fun h => hne (Units.ext h)
  set M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
    with hM
  have h₁₂ : M.toBlocks₁₂ = 0 := by
    ext i j
    exact eq_zero_of_commute_diagonal hm (i := Sum.inl i) (j := Sum.inr j) hdiff
  have h₂₁ : M.toBlocks₂₁ = 0 := by
    ext i j
    exact eq_zero_of_commute_diagonal hm (i := Sum.inr i) (j := Sum.inl j) (Ne.symm hdiff)
  have hblock : M = Matrix.fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    rw [h₁₂, h₂₁]
  set g₁ := M.toBlocks₁₁ with hg₁
  set g₂ := M.toBlocks₂₂ with hg₂
  have horth : ∀ x y : Fin m → K, (g₁ *ᵥ x) ⬝ᵥ (g₂ *ᵥ y) = x ⬝ᵥ y := by
    intro x y
    have := isometry_of_mem_orthGroup hgO (Sum.elim x y)
    rw [← hM, hblock, Matrix.fromBlocks_mulVec, largeEvenQPlus_eq, largeEvenQPlus_eq] at this
    simpa [Function.comp_def] using this
  have hT : g₁ᵀ * g₂ = 1 := by
    ext i j
    have := horth (Pi.single i 1) (Pi.single j 1)
    simpa [Matrix.mulVec_single_one, dotProduct, Pi.single_apply, Matrix.mul_apply,
      Matrix.one_apply, eq_comm] using this
  have hdet : g₁.det ≠ 0 := by
    have := congrArg Matrix.det hT
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
    exact left_ne_zero_of_mul_eq_one this
  set h := Matrix.GeneralLinearGroup.mkOfDetNeZero g₁ hdet with hh
  have hh1 : (h : Matrix (Fin m) (Fin m) K) = g₁ :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero g₁ hdet
  have hh2 : ((h⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)ᵀ = g₂ := by
    rw [Matrix.GeneralLinearGroup.coe_inv, hh1, Matrix.transpose_nonsing_inv]
    exact Matrix.inv_eq_right_inv hT
  refine ⟨h, Units.ext ?_⟩
  rw [coe_leviHom, hh1, hh2, ← hM]
  exact hblock.symm

theorem isQuasisimple_sl (hm : 3 ≤ m) :
    CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin m) K) := by
  have hperf := CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := m) (by omega) (Or.inl hm)
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := K) (n := m) (by omega) (Or.inl hm)
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hcomm
  push Not at hcomm
  have : IsMulCommutative (Matrix.SpecialLinearGroup (Fin m) K ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin m) K)) := ⟨⟨hcomm⟩⟩
  exact Group.IsPerfect.not_isMulCommutative _ this

@[expose] noncomputable def leviSL (K : Type) [Field K] (m : ℕ) :
    Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m ⊕ Fin m) K :=
  (leviHom K m).comp Matrix.SpecialLinearGroup.toGL

theorem leviSL_injective : Function.Injective (leviSL K m) :=
  leviHom_injective.comp Matrix.SpecialLinearGroup.toGL_injective

theorem range_leviSL_le (hm : 3 ≤ m) :
    (leviSL K m).range ≤ LargeEvenOmega (LargeEvenQPlus K m) := by
  have hO : (leviSL K m).range ≤ LargeEvenOrthGroup (LargeEvenQPlus K m) := by
    rintro _ ⟨s, rfl⟩
    exact leviHom_mem_orth _
  set T : Subgroup (Matrix.SpecialLinearGroup (Fin m) K) := ⊤ with hT
  have hperf : ⁅T, T⁆ = T := by
    have := (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := m) (by omega)
      (Or.inl hm)).commutator_eq_top
    simpa [commutator_def] using this
  calc (leviSL K m).range = T.map (leviSL K m) := MonoidHom.range_eq_map _
    _ = (⁅T, T⁆).map (leviSL K m) := by rw [hperf]
    _ = ⁅T.map (leviSL K m), T.map (leviSL K m)⁆ := Subgroup.map_commutator _ _ _
    _ ≤ ⁅LargeEvenOrthGroup (LargeEvenQPlus K m), LargeEvenOrthGroup (LargeEvenQPlus K m)⁆ := by
          have hrange : T.map (leviSL K m) = (leviSL K m).range := (MonoidHom.range_eq_map _).symm
          rw [hrange]
          exact Subgroup.commutator_mono hO hO
    _ = LargeEvenOmega (LargeEvenQPlus K m) := (largeEvenOmega_def _).symm

theorem isQuasisimple_range_leviSL (hm : 3 ≤ m) : CFSG.IsQuasisimple (leviSL K m).range :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective leviSL_injective)
    (isQuasisimple_sl hm)

theorem dgHom_mem_range_leviSL (u : Fin m → Kˣ) (hu : ∏ k, ((u k : Kˣ) : K) = 1) :
    dgHom K m u ∈ (leviSL K m).range := by
  have hdet : Matrix.GeneralLinearGroup.det (TauCeti.diagGL u : GL (Fin m) K) = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, TauCeti.diagGL_coe, Matrix.det_diagonal, hu,
      Units.val_one]
  have hmem : (TauCeti.diagGL u : GL (Fin m) K) ∈
      (Matrix.SpecialLinearGroup.toGL (n := Fin m) (R := K)).range := by
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet
  obtain ⟨s, hs⟩ := hmem
  refine ⟨s, ?_⟩
  change leviHom K m (Matrix.SpecialLinearGroup.toGL s) = dgHom K m u
  rw [hs]
  apply Units.ext
  rw [coe_leviHom, coe_dgHom, TauCeti.diagGL_coe]
  congr 1
  rw [← map_inv, TauCeti.diagGL_coe, Matrix.diagonal_transpose]
  rfl

@[expose] def tauPair (i j : Fin m) (c : Kˣ) : Fin m → Kˣ := Pi.mulSingle i c * Pi.mulSingle j c⁻¹

theorem prod_tauPair (i j : Fin m) (c : Kˣ) :
    ∏ k, (((tauPair i j c) k : Kˣ) : K) = 1 := by
  have h1 : ∀ (i : Fin m) (c : Kˣ), ∏ k : Fin m, (((Pi.mulSingle i c : Fin m → Kˣ) k : Kˣ) : K) =
      c := by
    intro i c
    simp [Pi.mulSingle_apply, apply_ite]
  simp only [tauPair, Pi.mul_apply, Units.val_mul, Finset.prod_mul_distrib, h1,
    Units.val_inv_eq_inv_val]
  exact mul_inv_cancel₀ c.ne_zero

theorem tauPair_pow {p : ℕ} {c : Kˣ} (hc : c ^ p = 1) (i j : Fin m) (k : Fin m) :
    (tauPair i j c k) ^ p = 1 := by
  have h : (tauPair i j c) ^ p = 1 := by
    rw [tauPair, mul_pow, ← Pi.mulSingle_pow, ← Pi.mulSingle_pow, inv_pow, hc, inv_one]
    simp
  exact congrFun h k

theorem plus_final_beta [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ} (hm : 4 ≤ m)
    {ν : Kˣ} (hνo : orderOf ν = p) {A D : Subgroup (GL (Fin m ⊕ Fin m) K)}
    (hT : IsFullTorus p A)
    (hE : EndData p (LargeEvenOmega (LargeEvenQPlus K m)) A D (dgHom K m (fun _ => ν))) :
    BigConcl p A D := by
  classical
  haveI := Fact.mk hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hνp : ν ^ p = 1 := hνo ▸ pow_orderOf_eq_one ν
  have hν2 : ν * ν ≠ 1 := by
    intro h
    have h2 : ν ^ 2 = 1 := by rw [sq]; exact h
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hνo] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  set Ω := LargeEvenOmega (LargeEvenQPlus K m) with hΩ
  set a := dgHom K m (fun _ => ν) with ha
  set Y : Subgroup (GL (Fin m ⊕ Fin m) K) := (leviSL K m).range with hY
  have hYΩ : Y ≤ Ω := range_leviSL_le (by omega)
  have hYc : ∀ y ∈ Y, y * a = a * y := by
    rintro _ ⟨s, rfl⟩
    exact leviHom_commute ν _
  have hcomm : ∀ g ∈ Ω, g * a = a * g → ∀ g' ∈ Ω, g' * a = a * g' →
      g * g' * g⁻¹ * g'⁻¹ ∈ Y := by
    intro g hg hgc g' hg' hg'c
    obtain ⟨h, rfl⟩ := exists_leviHom_eq hν2 hgc (omega_le_orth _ hg)
    obtain ⟨h', rfl⟩ := exists_leviHom_eq hν2 hg'c (omega_le_orth _ hg')
    have e : leviHom K m h * leviHom K m h' * (leviHom K m h)⁻¹ * (leviHom K m h')⁻¹ =
        leviHom K m (h * h' * h⁻¹ * h'⁻¹) := by simp only [map_mul, map_inv]
    rw [e]
    have hdet : Matrix.GeneralLinearGroup.det (h * h' * h⁻¹ * h'⁻¹) = 1 := by
      have := map_commutatorElement (Matrix.GeneralLinearGroup.det : GL (Fin m) K →* Kˣ) h h'
      rw [commutatorElement_def, commutatorElement_def] at this
      rw [this]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
    have hmem : (h * h' * h⁻¹ * h'⁻¹) ∈
        (Matrix.SpecialLinearGroup.toGL (n := Fin m) (R := K)).range := by
      rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
      exact hdet
    obtain ⟨s, hs⟩ := hmem
    exact ⟨s, by change leviHom K m (Matrix.SpecialLinearGroup.toGL s) = _; rw [hs]⟩
  have hYq : CFSG.IsQuasisimple Y := isQuasisimple_range_leviSL (by omega)
  have hDY : D ≤ Y := by
    have hperf : ⁅D, D⁆ = D := Subgroup.isPerfect_iff.1 hE.D_qs.1
    rw [← hperf]
    refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    rw [commutatorElement_def]
    exact hcomm x (hE.D_le hx) (hE.D_cent x hx) y (hE.D_le hy) (hE.D_cent y hy)
  have hDeq : D = Y := StdSubRestThree.eq_of_le_of_quasisimple hDY
    (fun b hb d hd => hE.D_norm b (hYΩ hb) (hYc b hb) d hd) hYq hE.D_qs
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
  set i3 : Fin m := ⟨3, by omega⟩ with hi3
  let u : (Fin 3 → Multiplicative (ZMod p)) → Fin m → Kˣ := fun f =>
    tauPair i0 i1 (z (f 0)) * tauPair i1 i2 (z (f 1)) * tauPair i2 i3 (z (f 2))
  have hup : ∀ f k, (u f k) ^ p = 1 := by
    intro f k
    simp only [u, Pi.mul_apply, mul_pow, tauPair_pow (hzp _), mul_one]
  have hprod : ∀ f, ∏ k, (((u f k : Kˣ)) : K) = 1 := by
    intro f
    simp only [u, Pi.mul_apply, Units.val_mul, Finset.prod_mul_distrib, prod_tauPair, mul_one]
  have hu0 : ∀ f, u f i0 = z (f 0) := by
    intro f
    simp [u, tauPair, Pi.mulSingle_apply, hi0, hi1, hi2, hi3, Fin.ext_iff]
  have hu1 : ∀ f, u f i1 = (z (f 0))⁻¹ * z (f 1) := by
    intro f
    simp [u, tauPair, Pi.mulSingle_apply, hi0, hi1, hi2, hi3, Fin.ext_iff]
  have hu2 : ∀ f, u f i2 = (z (f 1))⁻¹ * z (f 2) := by
    intro f
    simp [u, tauPair, Pi.mulSingle_apply, hi0, hi1, hi2, hi3, Fin.ext_iff]
  have hginj : Function.Injective fun f => dgHom K m (u f) := by
    intro f f' h
    have huf : u f = u f' := dgHom_injective h
    have e0 : f 0 = f' 0 := hzinj (by rw [← hu0 f, ← hu0 f', huf])
    have e1' : (z (f 0))⁻¹ * z (f 1) = (z (f' 0))⁻¹ * z (f' 1) := by
      rw [← hu1 f, ← hu1 f', huf]
    have e1 : f 1 = f' 1 := hzinj (by rw [e0] at e1'; exact mul_left_cancel e1')
    have e2' : (z (f 1))⁻¹ * z (f 2) = (z (f' 1))⁻¹ * z (f' 2) := by
      rw [← hu2 f, ← hu2 f', huf]
    have e2 : f 2 = f' 2 := hzinj (by rw [e1] at e2'; exact mul_left_cancel e2')
    funext j
    fin_cases j
    · exact e0
    · exact e1
    · exact e2
  have hgA : ∀ f, dgHom K m (u f) ∈ A := fun f => hT.2 (u f) (hup f)
  have hgY : ∀ f, dgHom K m (u f) ∈ Y := fun f => dgHom_mem_range_leviSL (u f) (hprod f)
  exact BigConcl.intro (A ⊓ D) (isElemAbelian_of_le hE.A_elem inf_le_left) inf_le_right
    inf_le_left (three_pow_le_card (A ⊓ D) (fun f => dgHom K m (u f)) hginj
      fun f => ⟨hgA f, hDeq ▸ hgY f⟩)

theorem IsFullTorus.map_conj {p : ℕ} {A : Subgroup (GL (Fin m ⊕ Fin m) K)}
    (hT : IsFullTorus p A) (s : GL (Fin m ⊕ Fin m) K) (τ : (Fin m → Kˣ) → Fin m → Kˣ)
    (hτ : ∀ u, s * dgHom K m u * s⁻¹ = dgHom K m (τ u))
    (hτp : ∀ u : Fin m → Kˣ, (∀ k, u k ^ p = 1) → ∀ k, τ u k ^ p = 1)
    (hτs : ∀ u' : Fin m → Kˣ, (∀ k, u' k ^ p = 1) → ∃ u : Fin m → Kˣ,
      (∀ k, u k ^ p = 1) ∧ τ u = u') :
    IsFullTorus p (A.map (MulAut.conj s).toMonoidHom) := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hT.1 x hx
    exact ⟨τ u, hτp u hu, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hτ]⟩
  · intro u' hu'
    obtain ⟨u, hu, rfl⟩ := hτs u' hu'
    exact ⟨dgHom K m u, hT.2 u hu, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hτ]⟩

theorem plus_reduce {p : ℕ} {A D : Subgroup (GL (Fin m ⊕ Fin m) K)} {a : GL (Fin m ⊕ Fin m) K}
    (hE : EndData p (LargeEvenOmega (LargeEvenQPlus K m)) A D a) (hT : IsFullTorus p A)
    (s : GL (Fin m ⊕ Fin m) K) (hs : s ∈ LargeEvenOrthGroup (LargeEvenQPlus K m))
    (τ : (Fin m → Kˣ) → Fin m → Kˣ) (hτ : ∀ u, s * dgHom K m u * s⁻¹ = dgHom K m (τ u))
    (hτp : ∀ u : Fin m → Kˣ, (∀ k, u k ^ p = 1) → ∀ k, τ u k ^ p = 1)
    (hτs : ∀ u' : Fin m → Kˣ, (∀ k, u' k ^ p = 1) → ∃ u : Fin m → Kˣ,
      (∀ k, u k ^ p = 1) ∧ τ u = u')
    (h : ∀ (A' D' : Subgroup (GL (Fin m ⊕ Fin m) K)),
      EndData p (LargeEvenOmega (LargeEvenQPlus K m)) A' D' (s * a * s⁻¹) →
        IsFullTorus p A' → BigConcl p A' D') : BigConcl p A D := by
  have hφ := map_conj_omega hs
  have h1 : EndData p (LargeEvenOmega (LargeEvenQPlus K m)) (A.map (MulAut.conj s).toMonoidHom)
      (D.map (MulAut.conj s).toMonoidHom) (s * a * s⁻¹) := by
    have := hE.map (MulAut.conj s) hφ
    simpa only [MulAut.conj_apply] using this
  exact BigConcl.of_map (MulAut.conj s) (h _ _ h1 (hT.map_conj s τ hτ hτp hτs))

theorem conj_dgHom_perm (σ : Equiv.Perm (Fin m)) (u : Fin m → Kˣ) :
    TauCeti.permutationGL (k := K) (Equiv.Perm.sumCongr σ σ) * dgHom K m u *
        (TauCeti.permutationGL (k := K) (Equiv.Perm.sumCongr σ σ))⁻¹ =
      dgHom K m (fun k => u (σ⁻¹ k)) := by
  rw [dgHom_apply, permutationGL_conj_diagGL, dgHom_apply]
  congr 1
  funext y
  rcases y with k | k
  · simp [pairedUnits, Equiv.Perm.sumCongr_inv]
  · simp [pairedUnits, Equiv.Perm.sumCongr_inv]

@[expose] def swapOnFun (F : Fin m → Prop) [DecidablePred F] :
    Fin m ⊕ Fin m → Fin m ⊕ Fin m
  | Sum.inl k => if F k then Sum.inr k else Sum.inl k
  | Sum.inr k => if F k then Sum.inl k else Sum.inr k

theorem swapOnFun_involutive (F : Fin m → Prop) [DecidablePred F] :
    Function.Involutive (swapOnFun F) := by
  intro y
  rcases y with k | k <;> by_cases h : F k <;> simp [swapOnFun, h]

@[expose] def swapOn (F : Fin m → Prop) [DecidablePred F] : Equiv.Perm (Fin m ⊕ Fin m) :=
  (swapOnFun_involutive F).toPerm

theorem swapOn_apply (F : Fin m → Prop) [DecidablePred F] (y : Fin m ⊕ Fin m) :
    swapOn F y = swapOnFun F y := rfl

theorem swapOn_inv (F : Fin m → Prop) [DecidablePred F] : (swapOn F)⁻¹ = swapOn F := by
  ext y
  rw [Equiv.Perm.inv_def]
  exact (swapOnFun_involutive F y).symm ▸ rfl

theorem largeEvenQPlus_comp_swapOn (F : Fin m → Prop) [DecidablePred F] (v : Fin m ⊕ Fin m → K) :
    LargeEvenQPlus K m (v ∘ swapOn F) = LargeEvenQPlus K m v := by
  simp only [largeEvenQPlus_def, Function.comp_apply, swapOn_apply, swapOnFun]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : F k <;> simp [h, mul_comm]

theorem swapOn_mem_orth (F : Fin m → Prop) [DecidablePred F] :
    TauCeti.permutationGL (k := K) (swapOn F) ∈ LargeEvenOrthGroup (LargeEvenQPlus K m) :=
  permutationGL_mem_orthPlus fun v => by rw [swapOn_inv, largeEvenQPlus_comp_swapOn]

theorem conj_dgHom_swapOn (F : Fin m → Prop) [DecidablePred F] (u : Fin m → Kˣ) :
    TauCeti.permutationGL (k := K) (swapOn F) * dgHom K m u *
        (TauCeti.permutationGL (k := K) (swapOn F))⁻¹ =
      dgHom K m (fun k => if F k then (u k)⁻¹ else u k) := by
  rw [dgHom_apply, permutationGL_conj_diagGL, dgHom_apply, swapOn_inv]
  congr 1
  funext y
  rcases y with k | k
  · by_cases h : F k <;> simp [pairedUnits, swapOn_apply, swapOnFun, h]
  · by_cases h : F k <;> simp [pairedUnits, swapOn_apply, swapOnFun, h]

theorem plus_toral [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m : ℕ} (hm : 4 ≤ m)
    {A D : Subgroup (GL (Fin m ⊕ Fin m) K)} {a : GL (Fin m ⊕ Fin m) K}
    (hE : EndData p (LargeEvenOmega (LargeEvenQPlus K m)) A D a) (hT : IsFullTorus p A) :
    BigConcl p A D := by
  classical
  haveI := Fact.mk hp
  obtain ⟨α, hα, rfl⟩ := hT.1 a hE.a_mem
  rcases plus_dichotomy hp hT hα hE with ⟨i₀, hi₀, hrest⟩ | hall
  ·
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    set σ : Equiv.Perm (Fin (k + 1)) := Equiv.swap i₀ (Fin.last k) with hσ
    have hord : orderOf (α i₀) = p := orderOf_eq_prime (hα i₀) hi₀
    refine plus_reduce hE hT (TauCeti.permutationGL (k := K) (Equiv.Perm.sumCongr σ σ))
      (sumCongr_mem_orthPlus σ) (fun u k => u (σ⁻¹ k)) (conj_dgHom_perm σ)
      (fun u hu k => hu _) (fun u' hu' => ⟨fun k => u' (σ k), fun k => hu' _, ?_⟩) ?_
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
      rw [conj_dgHom_perm, e] at hE'
      exact plus_final_alpha hp hp2 (by omega) hord hT' hE'
  ·
    have hi₀ : (⟨0, by omega⟩ : Fin m) = (⟨0, by omega⟩ : Fin m) := rfl
    set ν := α ⟨0, by omega⟩ with hν
    have hν1 : ν ≠ 1 := hall _
    have hord : orderOf ν = p := orderOf_eq_prime (hα _) hν1
    have hcls : ∀ k, α k = ν ∨ α k = ν⁻¹ := fun k =>
      plus_two_class hp hT hα hE (hall ⟨0, by omega⟩) (hall k)
    set F : Fin m → Prop := fun k => α k = ν⁻¹ with hF
    have hne : ν ≠ ν⁻¹ := by
      intro h
      have h2 : ν ^ 2 = 1 := by
        calc ν ^ 2 = ν * ν := sq ν
          _ = ν * ν⁻¹ := by rw [← h]
          _ = 1 := mul_inv_cancel ν
      have h3 := orderOf_dvd_of_pow_eq_one h2
      rw [hord] at h3
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
    refine plus_reduce hE hT (TauCeti.permutationGL (k := K) (swapOn F)) (swapOn_mem_orth F)
      (fun u k => if F k then (u k)⁻¹ else u k) (conj_dgHom_swapOn F)
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
      rw [conj_dgHom_swapOn, e] at hE'
      exact plus_final_beta hp hp2 hm hord hT' hE'

theorem plus_big [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) {m : ℕ} (hm : 4 ≤ m)
    {A D : Subgroup (GL (Fin m ⊕ Fin m) K)} {a : GL (Fin m ⊕ Fin m) K}
    (hE : EndData p (LargeEvenOmega (LargeEvenQPlus K m)) A D a) (hr : p ^ m ≤ Nat.card A) :
    BigConcl p A D := by
  haveI := Fact.mk hp
  obtain ⟨ζ, hζo, -, -, -⟩ := exists_zeta (K := K) hp hp2 hpK
  obtain ⟨g, hgO, χ, hχ, hsurj⟩ := exists_orth_conj_plus hp2 hζo
    (hE.A_le.trans (omega_le_orth _)) hE.A_elem hr
  refine BigConcl.of_map (MulAut.conj g) (plus_toral hp hp2 hm
    (hE.map (MulAut.conj g) (map_conj_omega hgO)) ?_)
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨fun k => χ k ⟨x, hx⟩, fun k => ?_, ?_⟩
    · rw [← map_pow]
      have : (⟨x, hx⟩ : A) ^ p = 1 := Subtype.ext (hE.A_elem.2 x hx)
      rw [this, map_one]
    · have := hχ ⟨x, hx⟩
      rw [dgHom_apply]
      simpa [MulAut.conj_apply] using this.symm
  · intro u hu
    obtain ⟨x, hx⟩ := hsurj u hu
    refine ⟨x, x.2, ?_⟩
    have := hχ x
    rw [dgHom_apply]
    have hu' : (fun k => χ k x) = u := funext hx
    rw [hu'] at this
    simpa [MulAut.conj_apply] using this

end PlusToral

theorem plusSplitInput_holds : PlusSplitInput := by
  intro K _ _ n m p hK hm hp hpn
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
  set e := projMkEquiv (scalars_subgroupOf_omegaPlus_eq_bot (K := K) (by omega : 1 ≤ m)) with he
  set f : OrthRest.RPlus K m →* GL (Fin m ⊕ Fin m) K :=
    (LargeEvenOmega (LargeEvenQPlus K m)).subtype.comp e.symm.toMonoidHom with hf
  have hfinj : Function.Injective f := fun x y h =>
    e.symm.injective (Subtype.ext h)
  have hfrange : f.range = LargeEvenOmega (LargeEvenQPlus K m) := by
    ext x
    constructor
    · rintro ⟨r, rfl⟩
      exact (e.symm r).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [hf]⟩
  exact eltNormSmall_of_ambient (LargeEvenOmega (LargeEvenQPlus K m)) f hfinj hfrange
    fun A D a hE hr => plus_big hp hp2 hpK hm hE hr

end SmallOrth

end CFSG.StandardType

end
