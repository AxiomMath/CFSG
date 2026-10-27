module

public import CFSG.RankThree.PartTwo.KFacts.KS222SL3Tools
public import CFSG.RankThree.PartOne.KF.R9Perm
import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item221ResProof.LeviMat

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.RankThree.PartOne.KFU (permGL coe_permGL permGL_conj_diagU diagU diagU_val)
open CFSG.RankThree.PartTwo.Sec21.SL3Lines (scalar_mul_comm det_conj inf_centralizer_conj
  diagUnits_eq_diagU diagUnits_one_one_one eq_one_of_mul_self_eq_one)

variable {K : Type} [Field K]

@[expose] noncomputable def levi0 : Subgroup (GL (Fin 3) K) :=
  (blockHom.comp (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K)).range

theorem levi0_hom_injective :
    Function.Injective (blockHom.comp
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K)) :=
  blockHom_injective.comp SpecialLinearGroup.toGL_injective

@[expose] noncomputable def levi0Equiv : SpecialLinearGroup (Fin 2) K ≃* levi0 (K := K) :=
  MonoidHom.ofInjective levi0_hom_injective

variable {n : ℕ}

theorem perfectResidual_centralizer_diagE_eq [Finite K] (hPi : PiField true 2 n K)
    (hK4 : 4 ≤ Nat.card K) {e : Kˣ} (he : e ≠ 1) :
    inSubgroup perfectResidual (slPi true 3 (2 ^ n) K ⊓ Subgroup.centralizer {diagE e}) =
      levi0 := by
  rw [centralizer_diagE_eq hPi he]
  set C := (glPi true 2 (2 ^ n) K).map blockHom with hC
  set ι : SpecialLinearGroup (Fin 2) K →* GL (Fin 3) K :=
    blockHom.comp (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K)
    with hι
  have hιinj : Function.Injective ι := levi0_hom_injective
  set B := ι.range with hB
  have hBC : B ≤ C := by
    rintro _ ⟨A, rfl⟩
    exact ⟨_, mem_glPi_true _ _, rfl⟩
  have hq := CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le (k := K) (m := 2) le_rfl hK4
  have hperf : Group.IsPerfect ↥B := by
    have := hq.1
    exact Group.IsPerfect.ofSurjective (f := (MonoidHom.ofInjective hιinj).toMonoidHom)
      (MonoidHom.ofInjective hιinj).surjective
  set eC := (glPi true 2 (2 ^ n) K).equivMapOfInjective blockHom blockHom_injective with heC
  set Φ : ↥C →* Kˣ := GeneralLinearGroup.det.comp
    ((glPi true 2 (2 ^ n) K).subtype.comp eC.symm.toMonoidHom) with hΦ
  have hker : Φ.ker = B.subgroupOf C := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      set B₀ := eC.symm c with hB₀
      have hdet : ((B₀ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
        rw [← GeneralLinearGroup.val_det_apply]
        exact congrArg Units.val h
      have hc : (c : GL (Fin 3) K) = blockHom (B₀ : GL (Fin 2) K) := by
        have := congrArg Subtype.val (eC.apply_symm_apply c)
        rw [← this]
        rfl
      refine ⟨⟨(B₀ : GL (Fin 2) K), hdet⟩, ?_⟩
      rw [hc]
      show blockHom (SpecialLinearGroup.toGL ⟨_, hdet⟩) = _
      congr 1
      exact Units.ext rfl
    · rintro ⟨A, hA⟩
      have hc : eC.symm c = ⟨SpecialLinearGroup.toGL A, mem_glPi_true _ _⟩ := by
        apply eC.injective
        rw [eC.apply_symm_apply]
        exact Subtype.ext hA.symm
      show GeneralLinearGroup.det ((eC.symm c : GL (Fin 2) K)) = 1
      rw [hc]
      apply Units.ext
      rw [GeneralLinearGroup.val_det_apply]
      exact A.2
  exact CFSG.RankThree.PartOne.KFU.inSubgroup_perfectResidual_eq_of_ker hBC hperf Φ hker

theorem mem_levi0_of_mul_self [CharP K 2] (hPi : PiField true 2 n K) {e : Kˣ} (he : e ≠ 1)
    {x : GL (Fin 3) K} (hx : x ∈ slPi true 3 (2 ^ n) K ⊓ Subgroup.centralizer {diagE e})
    (hxx : x * x = 1) : x ∈ levi0 := by
  rw [centralizer_diagE_eq hPi he] at hx
  obtain ⟨B, -, rfl⟩ := hx
  have hBB : B * B = 1 := blockHom_injective (by rw [map_mul, hxx, map_one])
  have hdet : ((GeneralLinearGroup.det B : Kˣ) : K) * (GeneralLinearGroup.det B : Kˣ) = 1 := by
    rw [← Units.val_mul, ← map_mul, hBB, map_one, Units.val_one]
  have hd1 := eq_one_of_mul_self_eq_one hdet
  refine ⟨⟨(B : Matrix (Fin 2) (Fin 2) K), ?_⟩, ?_⟩
  · rw [← GeneralLinearGroup.val_det_apply]
    exact hd1
  · show blockHom (SpecialLinearGroup.toGL _) = blockHom B
    congr 1
    exact Units.ext rfl

theorem det_permGL [CharP K 2] (σ : Equiv.Perm (Fin 3)) :
    ((permGL σ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [coe_permGL, det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h
  · rw [h]
    simp
  · rw [h]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    exact neg_one_eq_one_iff.mpr (ringChar.eq K 2 ▸ rfl)

theorem exists_conj_diagE {y g : GL (Fin 3) K} {l s t : Kˣ}
    (hy : g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t)
    (hst : ¬ (s = 1 ∧ t = 1)) (hnd : ¬ (s ≠ 1 ∧ t ≠ 1 ∧ s ≠ t)) :
    ∃ (σ : Equiv.Perm (Fin 3)) (l' e : Kˣ), e ≠ 1 ∧
      y = (g * permGL σ) * (GeneralLinearGroup.scalar (Fin 3) l' * diagE e) *
        (g * permGL σ)⁻¹ := by
  have hyg : y = g * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g⁻¹ := by
    rw [← hy]
    group
  obtain ⟨σ, l'', e, he, hw⟩ : ∃ (σ : Equiv.Perm (Fin 3)) (l'' e : Kˣ), e ≠ 1 ∧
      diagUnits 1 s t = permGL σ * (GeneralLinearGroup.scalar (Fin 3) l'' * diagE e) *
        (permGL σ)⁻¹ := by
    by_cases hs1 : s = 1
    · subst hs1
      have ht1 : t ≠ 1 := fun h => hst ⟨rfl, h⟩
      refine ⟨Equiv.swap 0 2, 1, t, ht1, ?_⟩
      rw [map_one, one_mul, diagE, diagUnits_eq_diagU, diagUnits_eq_diagU, permGL_conj_diagU]
      congr 1
      funext i
      fin_cases i <;> rfl
    · by_cases ht1 : t = 1
      · subst ht1
        refine ⟨Equiv.swap 0 1, 1, s, hs1, ?_⟩
        rw [map_one, one_mul, diagE, diagUnits_eq_diagU, diagUnits_eq_diagU, permGL_conj_diagU]
        congr 1
        funext i
        fin_cases i <;> rfl
      · have hst2 : s = t := by
          by_contra h
          exact hnd ⟨hs1, ht1, h⟩
        subst hst2
        refine ⟨1, s, s⁻¹, inv_ne_one.mpr hs1, ?_⟩
        rw [map_one, one_mul, inv_one, mul_one]
        apply Units.ext
        rw [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_diagE, coe_diagUnits,
          Matrix.scalar_apply, diagonal_mul_diagonal]
        congr 1
        funext i
        fin_cases i <;> simp
  refine ⟨σ, l * l'', e, he, ?_⟩
  rw [hyg, hw, map_mul]
  have h1 := scalar_mul_comm l (permGL σ)
  have h2 := scalar_mul_comm l (diagE e)
  have h3 := scalar_mul_comm l (permGL σ)⁻¹
  calc g * (GeneralLinearGroup.scalar (Fin 3) l * (permGL σ *
        (GeneralLinearGroup.scalar (Fin 3) l'' * diagE e) * (permGL σ)⁻¹)) * g⁻¹ =
      g * (GeneralLinearGroup.scalar (Fin 3) l * permGL σ) *
        (GeneralLinearGroup.scalar (Fin 3) l'' * diagE e) * (permGL σ)⁻¹ * g⁻¹ := by group
    _ = g * (permGL σ * GeneralLinearGroup.scalar (Fin 3) l) *
        (GeneralLinearGroup.scalar (Fin 3) l'' * diagE e) * (permGL σ)⁻¹ * g⁻¹ := by rw [h1]
    _ = g * permGL σ * (GeneralLinearGroup.scalar (Fin 3) l *
        GeneralLinearGroup.scalar (Fin 3) l'' * diagE e) * (g * permGL σ)⁻¹ := by group

theorem perfectResidual_centralizer_conj_eq [Finite K] (hPi : PiField true 2 n K)
    (hK4 : 4 ≤ Nat.card K) {e : Kˣ} (he : e ≠ 1) (u : GL (Fin 3) K) (l : Kˣ) :
    inSubgroup perfectResidual (slPi true 3 (2 ^ n) K ⊓
        Subgroup.centralizer {u * (GeneralLinearGroup.scalar (Fin 3) l * diagE e) * u⁻¹}) =
      levi0.map (MulAut.conj u).toMonoidHom := by
  rw [inf_centralizer_conj, ← GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _
    (MulAut.conj u).injective, perfectResidual_centralizer_diagE_eq hPi hK4 he]

theorem mem_perfectResidual_of_mul_self [Finite K] [CharP K 2] (hPi : PiField true 2 n K)
    (hK4 : 4 ≤ Nat.card K) {e : Kˣ} (he : e ≠ 1) (u : GL (Fin 3) K) (l : Kˣ)
    {x : GL (Fin 3) K} (hx : x ∈ slPi true 3 (2 ^ n) K ⊓
      Subgroup.centralizer {u * (GeneralLinearGroup.scalar (Fin 3) l * diagE e) * u⁻¹})
    (hxx : x * x = 1) :
    x ∈ inSubgroup perfectResidual (slPi true 3 (2 ^ n) K ⊓
      Subgroup.centralizer {u * (GeneralLinearGroup.scalar (Fin 3) l * diagE e) * u⁻¹}) := by
  rw [perfectResidual_centralizer_conj_eq hPi hK4 he u l]
  rw [inf_centralizer_conj] at hx
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  have hx₀x₀ : x₀ * x₀ = 1 := (MulAut.conj u).injective (by
    rw [map_mul, map_one]
    exact hxx)
  exact ⟨x₀, mem_levi0_of_mul_self hPi he hx₀ hx₀x₀, rfl⟩

theorem exists_mem_slPi_map_levi0 [CharP K 2] (q : ℕ) (g : GL (Fin 3) K)
    (σ₁ σ₂ : Equiv.Perm (Fin 3)) :
    ∃ h ∈ slPi true 3 q K, levi0.map (MulAut.conj (g * permGL σ₁)).toMonoidHom =
      (levi0.map (MulAut.conj (g * permGL σ₂)).toMonoidHom).map (MulAut.conj h).toMonoidHom := by
  refine ⟨g * permGL σ₁ * (g * permGL σ₂)⁻¹, ?_, ?_⟩
  · rw [mem_slPi_true]
    have h1 : g * permGL σ₁ * (g * permGL σ₂)⁻¹ = g * (permGL σ₁ * (permGL σ₂)⁻¹) * g⁻¹ := by
      group
    rw [h1, SL3Lines.det_conj, Units.val_mul, det_mul, det_permGL, one_mul,
      Matrix.coe_units_inv, det_nonsing_inv, det_permGL, Ring.inverse_one]
  · rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]

theorem commute_of_scalar {y g : GL (Fin 3) K} {l : Kˣ}
    (hy : g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 1 1)
    (M : GL (Fin 3) K) : M * y = y * M := by
  have hyg : y = g * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 1 1) * g⁻¹ := by
    rw [← hy]
    group
  rw [diagUnits_one_one_one, mul_one] at hyg
  have hgS : g * GeneralLinearGroup.scalar (Fin 3) l * g⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) l := by
    rw [← scalar_mul_comm, mul_assoc, mul_inv_cancel, mul_one]
  rw [hyg, hgS, scalar_mul_comm]

theorem commute_of_distinct {q : ℕ} {y g : GL (Fin 3) K} {l s t : Kˣ}
    (hy : g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t)
    (hs1 : s ≠ 1) (ht1 : t ≠ 1) (hst : s ≠ t) {M N : GL (Fin 3) K}
    (hM : M ∈ slPi true 3 q K ⊓ Subgroup.centralizer {y})
    (hN : N ∈ slPi true 3 q K ⊓ Subgroup.centralizer {y}) : M * N = N * M := by
  have hyg : y = g * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g⁻¹ := by
    rw [← hy]
    group
  rw [hyg, inf_centralizer_conj] at hM hN
  obtain ⟨M₀, hM₀, rfl⟩ := hM
  obtain ⟨N₀, hN₀, rfl⟩ := hN
  have h1s : (1 : K) ≠ (s : K) := fun h => hs1 (Units.ext h.symm)
  have h1t : (1 : K) ≠ (t : K) := fun h => ht1 (Units.ext h.symm)
  have hst2 : (s : K) ≠ (t : K) := fun h => hst (Units.ext h)
  have hd : ∀ X ∈ slPi true 3 q K ⊓ Subgroup.centralizer {diagUnits 1 s t},
      ∀ i j : Fin 3, i ≠ j → (X : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
    intro X hX i j hij
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hX).2
    have hc' := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hc
    simp only [Units.val_mul, coe_diagUnits] at hc'
    apply entry_eq_zero_of_commute_diagonal hc'
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      first | exact h1s | exact h1s.symm | exact h1t | exact h1t.symm | exact hst2 |
        exact hst2.symm | exact hs1 | exact ht1
  have hdiag : ∀ X ∈ slPi true 3 q K ⊓ Subgroup.centralizer {diagUnits 1 s t},
      (X : Matrix (Fin 3) (Fin 3) K) = diagonal (fun i => (X : Matrix (Fin 3) (Fin 3) K) i i) := by
    intro X hX
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [hd X hX i j hij, diagonal_apply_ne _ hij]
  have hc : M₀ * N₀ = N₀ * M₀ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hdiag M₀ hM₀, hdiag N₀ hN₀, diagonal_mul_diagonal,
      diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * M₀ * g⁻¹ * (g * N₀ * g⁻¹) = g * (M₀ * N₀) * g⁻¹ := by group
    _ = g * (N₀ * M₀) * g⁻¹ := by rw [hc]
    _ = g * N₀ * g⁻¹ * (g * M₀ * g⁻¹) := by group

theorem eq_one_of_distinct_of_mul_self [CharP K 2] {q : ℕ} {y g : GL (Fin 3) K} {l s t : Kˣ}
    (hy : g⁻¹ * y * g = GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t)
    (hs1 : s ≠ 1) (ht1 : t ≠ 1) (hst : s ≠ t) {M : GL (Fin 3) K}
    (hM : M ∈ slPi true 3 q K ⊓ Subgroup.centralizer {y}) (hMM : M * M = 1) : M = 1 := by
  have hyg : y = g * (GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t) * g⁻¹ := by
    rw [← hy]
    group
  rw [hyg, inf_centralizer_conj] at hM
  obtain ⟨M₀, hM₀, rfl⟩ := hM
  have h1s : (1 : K) ≠ (s : K) := fun h => hs1 (Units.ext h.symm)
  have h1t : (1 : K) ≠ (t : K) := fun h => ht1 (Units.ext h.symm)
  have hst2 : (s : K) ≠ (t : K) := fun h => hst (Units.ext h)
  have hz : ∀ i j : Fin 3, i ≠ j → (M₀ : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
    intro i j hij
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hM₀).2
    have hc' := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hc
    simp only [Units.val_mul, coe_diagUnits] at hc'
    apply entry_eq_zero_of_commute_diagonal hc'
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      first | exact h1s | exact h1s.symm | exact h1t | exact h1t.symm | exact hst2 |
        exact hst2.symm | exact hs1 | exact ht1
  have hM₀M₀ : M₀ * M₀ = 1 := (MulAut.conj g).injective (by
    rw [map_mul, map_one]
    exact hMM)
  have hxm := congrArg (fun z : GL (Fin 3) K => (z : Matrix (Fin 3) (Fin 3) K)) hM₀M₀
  simp only [Units.val_mul, Units.val_one] at hxm
  have hd0 : (M₀ : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
    apply eq_one_of_mul_self_eq_one
    have e := congrFun (congrFun hxm 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply_eq, hz 0 1 (by decide),
      hz 0 2 (by decide)] at e
    simpa using e
  have hd1 : (M₀ : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := by
    apply eq_one_of_mul_self_eq_one
    have e := congrFun (congrFun hxm 1) 1
    rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply_eq, hz 1 0 (by decide),
      hz 1 2 (by decide)] at e
    simpa using e
  have hd2 : (M₀ : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    apply eq_one_of_mul_self_eq_one
    have e := congrFun (congrFun hxm 2) 2
    rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply_eq, hz 2 0 (by decide),
      hz 2 1 (by decide)] at e
    simpa using e
  have hd : ∀ i, (M₀ : Matrix (Fin 3) (Fin 3) K) i i = 1 := by
    intro i
    fin_cases i
    exacts [hd0, hd1, hd2]
  have hM₀1 : M₀ = 1 := by
    apply Units.ext
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [hd, Units.val_one, Matrix.one_apply_eq]
    · rw [hz i j hij, Units.val_one, Matrix.one_apply_ne hij]
  rw [hM₀1, map_one]

end CFSG.RankThree.PartTwo.Sec21.Item221ResProof.LeviMat
