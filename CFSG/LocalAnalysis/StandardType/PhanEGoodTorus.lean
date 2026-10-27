module

public import CFSG.LocalAnalysis.StandardType.PhanEStdFamily

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary
open scoped MatrixGroups

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {w₀ : (coxeterMatrix D.isFiniteType).Group}
  {F : FrobData D n H w₀} {n₀ : K} (L : StdLevi F n₀)
  {G : Type} [Group G] {ρ : G →* K} (hρ : Function.Injective ρ) (hρr : ρ.range = stdFix F n₀)
  {Kf : Type} [Field Kf] [Finite Kf] {f : ℕ} [CharP Kf 2] (κ : Kf ≃+* L.Fld)
  (hκ : ∀ c, κ (unitaryInvolution Kf 2 f c) = L.θ (κ c))

theorem hmbGood_units_map_symm (a : L.Fldˣ) :
    Units.map κ.toMonoidHom (Units.map κ.symm.toMonoidHom a) = a := by
  ext
  simp

theorem hmbGood_suToSL_torusTwo (u : normOne (unitaryInvolution Kf 2 f)) :
    suToSL (f := f) κ 2 (torusTwo (unitaryInvolution Kf 2 f) u) =
      WeakCT.torusHom L.Fld (Units.map κ.toMonoidHom (u : Kfˣ)) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_suToSL, coe_torusTwo, WeakCT.coe_torusHom, Matrix.map_apply]

include hκ in
theorem hmbGood_normOne_units_map_symm {s : L.Fldˣ}
    (hs : L.θ (s : L.Fld) * (s : L.Fld) = 1) :
    Units.map κ.symm.toMonoidHom s ∈ normOne (unitaryInvolution Kf 2 f) := by
  rw [mem_normOne]
  apply κ.injective
  rw [map_mul, map_one, hκ]
  have hκs : κ (((Units.map κ.symm.toMonoidHom s : Kfˣ) : Kf)) = (s : L.Fld) := by simp
  rw [hκs]
  exact hs

include hκ in
theorem hmbGood_exists_torusTwo_of_suToSL_torusHom {a : Su Kf 2 f 2} {s : L.Fldˣ}
    (hA : suToSL (f := f) κ 2 a = WeakCT.torusHom L.Fld s) :
    ∃ u : normOne (unitaryInvolution Kf 2 f),
      torusTwo (unitaryInvolution Kf 2 f) u = a ∧ κ ((u : Kfˣ) : Kf) = (s : L.Fld) := by
  have hfix : WeakCT.torusHom L.Fld s ∈ slSU L.θ 2 := by
    rw [← hA, ← range_suToSL L.θ κ hκ 2]
    exact ⟨a, rfl⟩
  have h3 : (L.θ (s : L.Fld))⁻¹ = (s : L.Fld) := by
    have h := (mem_slSU_iff L.θ 2 (WeakCT.torusHom L.Fld s)).1 hfix
    rw [slSigma_torusHom] at h
    have h2 := (WeakCT.torusHom_injective (K := L.Fld) h)
    have h3 := congrArg (fun u : L.Fldˣ => (u : L.Fld)) h2
    simpa using h3
  have hθ : L.θ (s : L.Fld) = (s : L.Fld)⁻¹ := (inv_eq_iff_eq_inv).1 h3
  have hu : Units.map κ.symm.toMonoidHom s ∈ normOne (unitaryInvolution Kf 2 f) :=
    hmbGood_normOne_units_map_symm L κ hκ (by rw [hθ]; exact inv_mul_cancel₀ s.ne_zero)
  let u : normOne (unitaryInvolution Kf 2 f) := ⟨Units.map κ.symm.toMonoidHom s, hu⟩
  refine ⟨u, ?_, ?_⟩
  · apply suToSL_injective (f := f) κ 2
    have huu : Units.map κ.toMonoidHom (u : Kfˣ) = s := Units.ext (by simp [u])
    rw [hmbGood_suToSL_torusTwo, huu]
    exact hA.symm
  · show κ ((u : Kfˣ) : Kf) = (s : L.Fld)
    simp [u]

theorem hmbGood_mem_normalizer_of_conj_eq {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h : ∀ z ∈ H, g * z * g⁻¹ = z) : g ∈ Subgroup.normalizer (H : Set G) :=
  Subgroup.centralizer_le_normalizer _
    ((Subgroup.mem_centralizer_iff).2 fun z hz => by
      have hz' := h z hz
      have hcomm : g * z = z * g := by
        have := congrArg (· * g) hz'
        simpa [mul_assoc] using this
      exact hcomm.symm)

theorem hmbGood_normalizes_sl2
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    {i : Fin D.rank} {A : SL(2, L.Fld)} {y : K} (hy : y = L.ε i A)
    (hyT : y ∈ ⨆ k, H k) :
    (∀ c, ∃ d, A * sl2Upper c * A⁻¹ = sl2Upper d) ∧
      ∀ c, ∃ d, A * sl2Lower c * A⁻¹ = sl2Lower d := by
  have hroot : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hrootneg : -(Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hroot
  have htop : y ∈ Subgroup.normalizer (D.rootGroup (Pi.single i 1 : Fin D.rank → ℤ) : Set K) :=
    (iSup_le_normalizer_rootGroup hct hroot) hyT
  have hbot : y ∈
      Subgroup.normalizer (D.rootGroup (-(Pi.single i 1) : Fin D.rank → ℤ) : Set K) :=
    (iSup_le_normalizer_rootGroup hct hrootneg) hyT
  constructor
  · intro c
    have hgen : L.ε i (sl2Upper c) ∈ D.rootGroup (Pi.single i 1 : Fin D.rank → ℤ) :=
      (L.upper i).le ⟨c, rfl⟩
    have hmem := (Subgroup.mem_normalizer_iff.1 htop _).1 hgen
    rw [hy] at hmem
    rw [← map_mul, ← map_inv, ← map_mul] at hmem
    obtain ⟨d, hd⟩ := (L.upper i).ge hmem
    exact ⟨d, (L.ε_inj i) hd.symm⟩
  · intro c
    have hgen : L.ε i (sl2Lower c) ∈ D.rootGroup (-(Pi.single i 1) : Fin D.rank → ℤ) :=
      (L.lower i).le ⟨c, rfl⟩
    have hmem := (Subgroup.mem_normalizer_iff.1 hbot _).1 hgen
    rw [hy] at hmem
    rw [← map_mul, ← map_inv, ← map_mul] at hmem
    obtain ⟨d, hd⟩ := (L.lower i).ge hmem
    exact ⟨d, (L.ε_inj i) hd.symm⟩

theorem hmbGood_sl2_torus
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    {i : Fin D.rank} {A : SL(2, L.Fld)} {y : K} (hy : y = L.ε i A)
    (hyT : y ∈ ⨆ k, H k) :
    ∃ s : L.Fldˣ, A = WeakCT.torusHom L.Fld s := by
  obtain ⟨hu, hl⟩ := hmbGood_normalizes_sl2 L hct hy hyT
  exact sl2_eq_torusHom_of_normalizes A hu hl

theorem hmbGood_normalizer_blk_zero_upper
    (hext : SteinbergExtras D n H) {i j : Fin D.rank}
    (h2 : coxeterMatrix D.isFiniteType j i = 2) (B : SL(2, L.Fld)) :
    L.ε j B ∈ Subgroup.normalizer (D.rootGroup (Pi.single i 1 : Fin D.rank → ℤ) : Set K) :=
  hmbGood_mem_normalizer_of_conj_eq fun w hw => by
    obtain ⟨d, rfl⟩ := (L.upper i).ge hw
    rw [(L.ε_commute hext h2 B (sl2Upper d)).eq]
    group

theorem hmbGood_normalizer_blk_zero_lower
    (hext : SteinbergExtras D n H) {i j : Fin D.rank}
    (h2 : coxeterMatrix D.isFiniteType j i = 2) (B : SL(2, L.Fld)) :
    L.ε j B ∈
      Subgroup.normalizer (D.rootGroup (-(Pi.single i 1) : Fin D.rank → ℤ) : Set K) :=
  hmbGood_mem_normalizer_of_conj_eq fun w hw => by
    obtain ⟨d, rfl⟩ := (L.lower i).ge hw
    rw [(L.ε_commute hext h2 B (sl2Lower d)).eq]
    group

theorem hmbGood_sl2_torus_prod
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
    {i j : Fin D.rank} (h2 : coxeterMatrix D.isFiniteType i j = 2)
    {a b : Su Kf 2 f 2} {y : K}
    (hy : y = L.ε i (suToSL (f := f) κ 2 a) * L.ε j (suToSL (f := f) κ 2 b))
    (hyT : y ∈ ⨆ k, H k) :
    (∃ s : L.Fldˣ, suToSL (f := f) κ 2 a = WeakCT.torusHom L.Fld s) ∧
      ∃ t : L.Fldˣ, suToSL (f := f) κ 2 b = WeakCT.torusHom L.Fld t := by
  have h2' : coxeterMatrix D.isFiniteType j i = 2 :=
    (CoxeterMatrix.symmetric (coxeterMatrix D.isFiniteType) j i).trans h2
  have hroot : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hrootneg : -(Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hroot
  have hBnorm : L.ε j (suToSL (f := f) κ 2 b) ∈
      Subgroup.normalizer (D.rootGroup (Pi.single i 1 : Fin D.rank → ℤ) : Set K) :=
    hmbGood_normalizer_blk_zero_upper L hext h2'
      (suToSL (f := f) κ 2 b)
  have hBnormneg : L.ε j (suToSL (f := f) κ 2 b) ∈
      Subgroup.normalizer (D.rootGroup (-(Pi.single i 1) : Fin D.rank → ℤ) : Set K) :=
    hmbGood_normalizer_blk_zero_lower L hext h2'
      (suToSL (f := f) κ 2 b)
  have hAnorm : L.ε i (suToSL (f := f) κ 2 a) ∈
      Subgroup.normalizer (D.rootGroup (Pi.single i 1 : Fin D.rank → ℤ) : Set K) := by
    have hyN : y ∈ Subgroup.normalizer (D.rootGroup (Pi.single i 1 : Fin D.rank → ℤ) : Set K) :=
      (iSup_le_normalizer_rootGroup hct hroot) hyT
    have hsplit : L.ε i (suToSL (f := f) κ 2 a) =
        y * (L.ε j (suToSL (f := f) κ 2 b))⁻¹ := by
      rw [hy]
      group
    rw [hsplit]
    exact mul_mem hyN (inv_mem hBnorm)
  have hAnormneg : L.ε i (suToSL (f := f) κ 2 a) ∈
      Subgroup.normalizer (D.rootGroup (-(Pi.single i 1) : Fin D.rank → ℤ) : Set K) := by
    have hyN : y ∈
        Subgroup.normalizer (D.rootGroup (-(Pi.single i 1) : Fin D.rank → ℤ) : Set K) :=
      (iSup_le_normalizer_rootGroup hct hrootneg) hyT
    have hsplit : L.ε i (suToSL (f := f) κ 2 a) =
        y * (L.ε j (suToSL (f := f) κ 2 b))⁻¹ := by
      rw [hy]
      group
    rw [hsplit]
    exact mul_mem hyN (inv_mem hBnormneg)
  constructor
  · apply sl2_eq_torusHom_of_normalizes
    · intro c
      have hgen : L.ε i (sl2Upper c) ∈ D.rootGroup (Pi.single i 1 : Fin D.rank → ℤ) :=
        (L.upper i).le ⟨c, rfl⟩
      have hmem := (Subgroup.mem_normalizer_iff.1 hAnorm _).1 hgen
      rw [← map_mul, ← map_inv, ← map_mul] at hmem
      obtain ⟨d, hd⟩ := (L.upper i).ge hmem
      exact ⟨d, (L.ε_inj i) hd.symm⟩
    · intro c
      have hgen : L.ε i (sl2Lower c) ∈ D.rootGroup (-(Pi.single i 1) : Fin D.rank → ℤ) :=
        (L.lower i).le ⟨c, rfl⟩
      have hmem := (Subgroup.mem_normalizer_iff.1 hAnormneg _).1 hgen
      rw [← map_mul, ← map_inv, ← map_mul] at hmem
      obtain ⟨d, hd⟩ := (L.lower i).ge hmem
      exact ⟨d, (L.ε_inj i) hd.symm⟩
  ·
    have hAnorm' : L.ε i (suToSL (f := f) κ 2 a) ∈
        Subgroup.normalizer (D.rootGroup (Pi.single j 1 : Fin D.rank → ℤ) : Set K) :=
      hmbGood_normalizer_blk_zero_upper L hext h2 (suToSL (f := f) κ 2 a)
    have hAnorm'neg : L.ε i (suToSL (f := f) κ 2 a) ∈
        Subgroup.normalizer (D.rootGroup (-(Pi.single j 1) : Fin D.rank → ℤ) : Set K) :=
      hmbGood_normalizer_blk_zero_lower L hext h2 (suToSL (f := f) κ 2 a)
    have hrootj : (Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots :=
      (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j
    have hrootjneg : -(Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots :=
      (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hrootj
    have hBnorm' : L.ε j (suToSL (f := f) κ 2 b) ∈
        Subgroup.normalizer (D.rootGroup (Pi.single j 1 : Fin D.rank → ℤ) : Set K) := by
      have hyN : y ∈
          Subgroup.normalizer (D.rootGroup (Pi.single j 1 : Fin D.rank → ℤ) : Set K) :=
        (iSup_le_normalizer_rootGroup hct hrootj) hyT
      have hsplit : L.ε j (suToSL (f := f) κ 2 b) =
          y * (L.ε i (suToSL (f := f) κ 2 a))⁻¹ := by
        rw [hy, (L.ε_commute hext h2 (suToSL (f := f) κ 2 a)
          (suToSL (f := f) κ 2 b)).eq]
        group
      rw [hsplit]
      exact mul_mem hyN (inv_mem hAnorm')
    have hBnorm'neg : L.ε j (suToSL (f := f) κ 2 b) ∈
        Subgroup.normalizer (D.rootGroup (-(Pi.single j 1) : Fin D.rank → ℤ) : Set K) := by
      have hyN : y ∈
          Subgroup.normalizer (D.rootGroup (-(Pi.single j 1) : Fin D.rank → ℤ) : Set K) :=
        (iSup_le_normalizer_rootGroup hct hrootjneg) hyT
      have hsplit : L.ε j (suToSL (f := f) κ 2 b) =
          y * (L.ε i (suToSL (f := f) κ 2 a))⁻¹ := by
        rw [hy, (L.ε_commute hext h2 (suToSL (f := f) κ 2 a)
          (suToSL (f := f) κ 2 b)).eq]
        group
      rw [hsplit]
      exact mul_mem hyN (inv_mem hAnorm'neg)
    apply sl2_eq_torusHom_of_normalizes
    · intro c
      have hgen : L.ε j (sl2Upper c) ∈ D.rootGroup (Pi.single j 1 : Fin D.rank → ℤ) :=
        (L.upper j).le ⟨c, rfl⟩
      have hmem := (Subgroup.mem_normalizer_iff.1 hBnorm' _).1 hgen
      rw [← map_mul, ← map_inv, ← map_mul] at hmem
      obtain ⟨d, hd⟩ := (L.upper j).ge hmem
      exact ⟨d, (L.ε_inj j) hd.symm⟩
    · intro c
      have hgen : L.ε j (sl2Lower c) ∈ D.rootGroup (-(Pi.single j 1) : Fin D.rank → ℤ) :=
        (L.lower j).le ⟨c, rfl⟩
      have hmem := (Subgroup.mem_normalizer_iff.1 hBnorm'neg _).1 hgen
      rw [← map_mul, ← map_inv, ← map_mul] at hmem
      obtain ⟨d, hd⟩ := (L.lower j).ge hmem
      exact ⟨d, (L.ε_inj j) hd.symm⟩

theorem hmbGood_normalizes_sl3_upper
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    {i j : Fin D.rank} (hij : i < j) (h3 : coxeterMatrix D.isFiniteType i j = 3)
    {A : SL(3, L.Fld)} {y : K} (hy : y = L.ε₂ i j A) (hyT : y ∈ ⨆ k, H k)
    {s : Fin 2} {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots)
    (hrange : Set.range (fun c => L.ε₂ i j (WeakCT.blk L.Fld s (sl2Upper c))) =
      (D.rootGroup γ : Set K)) (c : L.Fld) :
    ∃ d, A * WeakCT.blk L.Fld s (sl2Upper c) * A⁻¹ =
      WeakCT.blk L.Fld s (sl2Upper d) := by
  have hgen : L.ε₂ i j (WeakCT.blk L.Fld s (sl2Upper c)) ∈ D.rootGroup γ :=
    hrange.le ⟨c, rfl⟩
  have hmem := (Subgroup.mem_normalizer_iff.1
    ((iSup_le_normalizer_rootGroup hct hγ) hyT) _).1 hgen
  rw [hy] at hmem
  rw [← map_mul, ← map_inv, ← map_mul] at hmem
  obtain ⟨d, hd⟩ := hrange.ge hmem
  exact ⟨d, (L.ε₂_inj i j hij h3) hd.symm⟩

theorem hmbGood_normalizes_sl3_lower
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    {i j : Fin D.rank} (hij : i < j) (h3 : coxeterMatrix D.isFiniteType i j = 3)
    {A : SL(3, L.Fld)} {y : K} (hy : y = L.ε₂ i j A) (hyT : y ∈ ⨆ k, H k)
    {s : Fin 2} {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots)
    (hrange : Set.range (fun c => L.ε₂ i j (WeakCT.blk L.Fld s (sl2Lower c))) =
      (D.rootGroup γ : Set K)) (c : L.Fld) :
    ∃ d, A * WeakCT.blk L.Fld s (sl2Lower c) * A⁻¹ =
      WeakCT.blk L.Fld s (sl2Lower d) := by
  have hgen : L.ε₂ i j (WeakCT.blk L.Fld s (sl2Lower c)) ∈ D.rootGroup γ :=
    hrange.le ⟨c, rfl⟩
  have hmem := (Subgroup.mem_normalizer_iff.1
    ((iSup_le_normalizer_rootGroup hct hγ) hyT) _).1 hgen
  rw [hy] at hmem
  rw [← map_mul, ← map_inv, ← map_mul] at hmem
  obtain ⟨d, hd⟩ := hrange.ge hmem
  exact ⟨d, (L.ε₂_inj i j hij h3) hd.symm⟩

theorem hmbGood_range_blk_zero_upper {i j : Fin D.rank} (hij : i < j)
    (h3 : coxeterMatrix D.isFiniteType i j = 3) :
    Set.range (fun c => L.ε₂ i j (WeakCT.blk L.Fld 0 (sl2Upper c))) =
      (D.rootGroup (Pi.single i 1) : Set K) := by
  rw [show (fun c => L.ε₂ i j (WeakCT.blk L.Fld 0 (sl2Upper c))) =
      (fun c => L.ε i (sl2Upper c)) from funext fun c =>
        DFunLike.congr_fun (L.ε₂_left i j hij h3) (sl2Upper c), L.upper i]

theorem hmbGood_range_blk_zero_lower {i j : Fin D.rank} (hij : i < j)
    (h3 : coxeterMatrix D.isFiniteType i j = 3) :
    Set.range (fun c => L.ε₂ i j (WeakCT.blk L.Fld 0 (sl2Lower c))) =
      (D.rootGroup (-(Pi.single i 1)) : Set K) := by
  rw [show (fun c => L.ε₂ i j (WeakCT.blk L.Fld 0 (sl2Lower c))) =
      (fun c => L.ε i (sl2Lower c)) from funext fun c =>
        DFunLike.congr_fun (L.ε₂_left i j hij h3) (sl2Lower c), L.lower i]

theorem hmbGood_range_blk_one_upper {i j : Fin D.rank} (hij : i < j)
    (h3 : coxeterMatrix D.isFiniteType i j = 3) :
    Set.range (fun c => L.ε₂ i j (WeakCT.blk L.Fld 1 (sl2Upper c))) =
      (D.rootGroup (Pi.single j 1) : Set K) := by
  rw [show (fun c => L.ε₂ i j (WeakCT.blk L.Fld 1 (sl2Upper c))) =
      (fun c => L.ε j (sl2Upper c)) from funext fun c =>
        DFunLike.congr_fun (L.ε₂_right i j hij h3) (sl2Upper c), L.upper j]

theorem hmbGood_range_blk_one_lower {i j : Fin D.rank} (hij : i < j)
    (h3 : coxeterMatrix D.isFiniteType i j = 3) :
    Set.range (fun c => L.ε₂ i j (WeakCT.blk L.Fld 1 (sl2Lower c))) =
      (D.rootGroup (-(Pi.single j 1)) : Set K) := by
  rw [show (fun c => L.ε₂ i j (WeakCT.blk L.Fld 1 (sl2Lower c))) =
      (fun c => L.ε j (sl2Lower c)) from funext fun c =>
        DFunLike.congr_fun (L.ε₂_right i j hij h3) (sl2Lower c), L.lower j]

theorem hmbGood_sl3_torus
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    {i j : Fin D.rank} (hij : i < j) (h3 : coxeterMatrix D.isFiniteType i j = 3)
    {A : SL(3, L.Fld)} {y : K} (hy : y = L.ε₂ i j A) (hyT : y ∈ ⨆ k, H k) :
    ∃ s t : L.Fldˣ, A = WeakCT.blk L.Fld 0 (WeakCT.torusHom L.Fld s) *
      WeakCT.blk L.Fld 1 (WeakCT.torusHom L.Fld t) := by
  have hrooti : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hrootj : (Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j
  refine sl3_eq_of_normalizes A ?_
  intro s c
  fin_cases s
  · refine ⟨hmbGood_normalizes_sl3_upper L hct hij h3 hy hyT hrooti
      (hmbGood_range_blk_zero_upper L hij h3) c,
      hmbGood_normalizes_sl3_lower L hct hij h3 hy hyT
        ((RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hrooti)
        (hmbGood_range_blk_zero_lower L hij h3) c⟩
  · refine ⟨hmbGood_normalizes_sl3_upper L hct hij h3 hy hyT hrootj
      (hmbGood_range_blk_one_upper L hij h3) c,
      hmbGood_normalizes_sl3_lower L hct hij h3 hy hyT
        ((RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hrootj)
        (hmbGood_range_blk_one_lower L hij h3) c⟩

theorem hmbGood_blk_torus_mem_slSU {s t : L.Fldˣ}
    (h : WeakCT.blk L.Fld 0 (WeakCT.torusHom L.Fld s) *
      WeakCT.blk L.Fld 1 (WeakCT.torusHom L.Fld t) ∈ slSU L.θ 3) :
    L.θ (s : L.Fld) * (s : L.Fld) = 1 ∧ L.θ (t : L.Fld) * (t : L.Fld) = 1 := by
  have hfix := (mem_slSU_iff L.θ 3 _).1 h
  have h' : WeakCT.blk L.Fld 0
        (WeakCT.torusHom L.Fld (Units.map L.θ.toMonoidHom s)⁻¹) *
      WeakCT.blk L.Fld 1 (WeakCT.torusHom L.Fld (Units.map L.θ.toMonoidHom t)⁻¹) =
      WeakCT.blk L.Fld 0 (WeakCT.torusHom L.Fld s) *
      WeakCT.blk L.Fld 1 (WeakCT.torusHom L.Fld t) := by
    rw [← hfix, map_mul, slSigma_blk, slSigma_blk, slSigma_torusHom, slSigma_torusHom]
  have hmat := congrArg (fun g : SL(3, L.Fld) => (g : Matrix (Fin 3) (Fin 3) L.Fld)) h'
  constructor
  · have e := congrFun (congrFun hmat 0) 0
    simp [WeakCT.blk, WeakCT.coe_blockSL_three_zero, WeakCT.coe_blockSL_three_one,
      WeakCT.coe_torusHom, Matrix.mul_apply, Fin.sum_univ_three] at e
    have he : L.θ (s : L.Fld) = (s : L.Fld)⁻¹ := (inv_eq_iff_eq_inv).1 e
    rw [he]
    exact inv_mul_cancel₀ s.ne_zero
  · have e := congrFun (congrFun hmat 2) 2
    simp [WeakCT.blk, WeakCT.coe_blockSL_three_zero, WeakCT.coe_blockSL_three_one,
      WeakCT.coe_torusHom, Matrix.mul_apply, Fin.sum_univ_three] at e
    have he : L.θ (t : L.Fld) = (t : L.Fld)⁻¹ := e
    rw [he]
    exact inv_mul_cancel₀ t.ne_zero

end CFSG.ClassicalInvolution.Phan.PhanE
