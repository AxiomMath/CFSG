module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65G2FixDim

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint.Chevalley CFSG.AGLEmbedding.KFactProofs.G2Q

private def sigma (α : Fin Tag.G2.rank → ℤ) : Fin Tag.G2.rank → ℤ :=
  reflect .G2 ia (reflect .G2 ir (reflect .G2 ia (reflect .G2 ir α)))

private def rep : Fin 4 → (Fin Tag.G2.rank → ℤ) :=
  ![![-2, -3], ![-1, -3], ![-1, -2], ![-1, -1]]

private theorem g2AdjFixDim_inv {L : Type} [Field L] (x : ModGL .G2 L) :
    g2AdjFixDim x⁻¹ = g2AdjFixDim x := by
  unfold g2AdjFixDim
  have h : LinearMap.ker (((x⁻¹ : ModGL .G2 L) : Module.End L (RootModule .G2 L)) - 1)
      = LinearMap.ker (((x : ModGL .G2 L) : Module.End L (RootModule .G2 L)) - 1) := by
    apply Submodule.ext
    intro v
    rw [LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sub_apply,
      sub_eq_zero, sub_eq_zero]
    constructor
    · intro hv
      have hc := congrArg (fun w => (x : Module.End L (RootModule .G2 L)) w) hv
      rw [← Module.End.mul_apply, Units.mul_inv x] at hc
      exact hc.symm
    · intro hv
      have hc := congrArg
        (fun w => ((x⁻¹ : ModGL .G2 L) : Module.End L (RootModule .G2 L)) w) hv
      rw [← Module.End.mul_apply, Units.inv_mul x] at hc
      exact hc.symm
  rw [h]

private theorem root_orbit (α : Fin Tag.G2.rank → ℤ)
    (hα : IsRoot .G2 α) :
    α = rep 0 ∨ sigma α = rep 0 ∨ sigma (sigma α) = rep 0 ∨
    α = rep 1 ∨ sigma α = rep 1 ∨ sigma (sigma α) = rep 1 ∨
    α = rep 2 ∨ sigma α = rep 2 ∨ sigma (sigma α) = rep 2 ∨
    α = rep 3 ∨ sigma α = rep 3 ∨ sigma (sigma α) = rep 3 := by
  obtain ⟨k, hk, hkr⟩ :=
    RootCertificate.exists_root_eq (C := Tag.rootCertificate Tag.G2)
      (Tag.rootCertificate_check Tag.G2) hα
  have hlen : (Tag.rootCertificate Tag.G2).roots.length = 12 := rfl
  rw [hlen] at hk
  rw [← hkr]
  interval_cases k <;> decide +kernel

private theorem tz_hVec {L : Type} [Field L]
    (s t : Lˣ) (j : Fin Tag.G2.rank) :
    ((tz s t : ModGL .G2 L) : Module.End L (RootModule .G2 L)) (hVec .G2 L j)
      = hVec .G2 L j := by
  simp only [tz, Units.val_mul, Module.End.mul_apply, torusElt_hVec]

private theorem tz_rootVec {L : Type} [Field L]
    (s t : Lˣ) {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) :
    ∃ χ : L, χ ≠ 0 ∧
      ((tz s t : ModGL .G2 L) : Module.End L (RootModule .G2 L)) (rootVec .G2 L α)
        = χ • rootVec .G2 L α := by
  refine ⟨((t ^ (∑ j, Tag.G2.cartan ir j * α j) *
    s ^ (∑ j, Tag.G2.cartan ia j * α j) : Lˣ) : L), ?_, ?_⟩
  · exact (t ^ _ * s ^ _ : Lˣ).ne_zero
  · simp only [tz]
    rw [Units.val_mul, Module.End.mul_apply, torusElt_rootVec ir t hα, map_smul,
      torusElt_rootVec ia s hα, smul_smul, ← Units.val_mul]

private theorem weyl1_rootVec {L : Type} [Field L]
    (i : Fin Tag.G2.rank) {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) :
    ∃ c : L, c ≠ 0 ∧
      ((weylElt .G2 L i (1 : Lˣ) : ModGL .G2 L) :
          Module.End L (RootModule .G2 L)) (rootVec .G2 L α)
        = c • rootVec .G2 L (reflect .G2 i α) ∧ IsRoot .G2 (reflect .G2 i α) := by
  refine ⟨(-1 : L) ^ stringDown .G2 i α *
    ↑((1 : Lˣ) ^ (-∑ j, Tag.G2.cartan i j * α j)), ?_, weylElt_rootVec i 1 hα,
    IsRoot.reflect i hα⟩
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by simp)

private theorem yq_rootVec {L : Type} [Field L]
    {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) :
    ∃ c : L, c ≠ 0 ∧
      ((yq : ModGL .G2 L) : Module.End L (RootModule .G2 L)) (rootVec .G2 L α)
        = c • rootVec .G2 L (sigma α) ∧ IsRoot .G2 (sigma α) := by
  obtain ⟨c0, hc0, e0, hr0⟩ := weyl1_rootVec (L := L) ir hα
  obtain ⟨c1, hc1, e1, hr1⟩ := weyl1_rootVec (L := L) ia hr0
  obtain ⟨c2, hc2, e2, hr2⟩ := weyl1_rootVec (L := L) ir hr1
  obtain ⟨c3, hc3, e3, hr3⟩ := weyl1_rootVec (L := L) ia hr2
  exact ⟨((c0 * c1) * c2) * c3,
    mul_ne_zero (mul_ne_zero (mul_ne_zero hc0 hc1) hc2) hc3, by
      simp only [yq, n0, n1, Units.val_mul, Module.End.mul_apply, e0, e1, e2, e3, map_smul,
        smul_smul]
      ring_nf
      rfl,
    hr3⟩

private noncomputable def xEnd {L : Type} [Field L]
    (s t : Lˣ) : Module.End L (RootModule .G2 L) :=
  (((tz s t : ModGL .G2 L) * (yq : ModGL .G2 L) : ModGL .G2 L) :
    Module.End L (RootModule .G2 L))

private theorem single_inr_eq_rootVec {L : Type} [Field L] {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) :
    Finsupp.single (Sum.inr ⟨α, hα⟩) 1 = rootVec .G2 L α :=
  (rootVec_eq_single_of_isRoot hα).symm

private theorem yq_hVec_ia {L : Type} [Field L] :
    ((yq : ModGL .G2 L) : Module.End L (RootModule .G2 L)) (hVec .G2 L ia)
      = hVec .G2 L ia - hVec .G2 L ir := by
  simp only [yq, n0, n1, Units.val_mul, Module.End.mul_apply, map_sub, map_smul, weylElt_hVec,
    cartan_ia_ia, cartan_ia_ir, cartan_ir_ia, cartan_ir_ir]
  norm_num
  module

private theorem yq_hVec_ir {L : Type} [Field L] :
    ((yq : ModGL .G2 L) : Module.End L (RootModule .G2 L)) (hVec .G2 L ir)
      = (3 : L) • hVec .G2 L ia - (2 : L) • hVec .G2 L ir := by
  simp only [yq, n0, n1, Units.val_mul, Module.End.mul_apply, map_sub, map_smul, weylElt_hVec,
    cartan_ia_ia, cartan_ia_ir, cartan_ir_ia, cartan_ir_ir]
  norm_num
  module

private theorem xEnd_hVec_ia {L : Type} [Field L]
    (s t : Lˣ) :
    xEnd s t (hVec .G2 L ia) = hVec .G2 L ia - hVec .G2 L ir := by
  simp only [xEnd, Units.val_mul, Module.End.mul_apply, yq_hVec_ia, map_sub, tz_hVec]

private theorem xEnd_hVec_ir {L : Type} [Field L]
    (s t : Lˣ) :
    xEnd s t (hVec .G2 L ir) = (3 : L) • hVec .G2 L ia - (2 : L) • hVec .G2 L ir := by
  simp only [xEnd, Units.val_mul, Module.End.mul_apply, yq_hVec_ir, map_sub, map_smul,
    tz_hVec]

private theorem xEnd_rootVec {L : Type} [Field L]
    (s t : Lˣ) {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) :
    ∃ d : L, d ≠ 0 ∧
      xEnd s t (rootVec .G2 L α) = d • rootVec .G2 L (sigma α) ∧ IsRoot .G2 (sigma α) := by
  obtain ⟨c, hc, he, hσ⟩ := yq_rootVec (L := L) hα
  obtain ⟨χ, hχ, htz⟩ := tz_rootVec (L := L) s t hσ
  refine ⟨c * χ, mul_ne_zero hc hχ, ?_, hσ⟩
  simp only [xEnd, Units.val_mul, Module.End.mul_apply, he, map_smul, htz, smul_smul]

private theorem sigma_injective : Function.Injective sigma := by
  have hia : Function.Injective (reflect .G2 ia) := fun x y h => by
    have h' : reflect .G2 ia (reflect .G2 ia x) = reflect .G2 ia (reflect .G2 ia y) :=
      congrArg (reflect .G2 ia) h
    rw [CFSG.Blueprint.Chevalley.reflect_reflect .G2 ia x,
      CFSG.Blueprint.Chevalley.reflect_reflect .G2 ia y] at h'
    exact h'
  have hir : Function.Injective (reflect .G2 ir) := fun x y h => by
    have h' : reflect .G2 ir (reflect .G2 ir x) = reflect .G2 ir (reflect .G2 ir y) :=
      congrArg (reflect .G2 ir) h
    rw [CFSG.Blueprint.Chevalley.reflect_reflect .G2 ir x,
      CFSG.Blueprint.Chevalley.reflect_reflect .G2 ir y] at h'
    exact h'
  exact hia.comp (hir.comp (hia.comp hir))

private theorem ia_ne_ir : ia ≠ ir := by decide

private theorem ir_ne_ia : ir ≠ ia := by decide

private theorem rootVec_apply_inl {L : Type} [Field L] {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α)
    (i : Fin Tag.G2.rank) : (rootVec .G2 L α) (Sum.inl i) = 0 := by
  rw [rootVec_eq_single_of_isRoot hα, Finsupp.single_apply]
  simp

private theorem rootVec_apply_inr {L : Type} [Field L] (β : Fin Tag.G2.rank → ℤ) (hβ : IsRoot .G2 β)
    {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) :
    (rootVec .G2 L α) (Sum.inr ⟨β, hβ⟩) = if α = β then 1 else 0 := by
  rw [rootVec_eq_single_of_isRoot hα, Finsupp.single_apply]
  by_cases h : α = β <;> simp [h]

private theorem lapply_inl_rootVec {L : Type} [Field L] (i : Fin Tag.G2.rank) {α : Fin Tag.G2.rank → ℤ}
    (hα : IsRoot .G2 α) :
    (Finsupp.lapply (Sum.inl i) : RootModule .G2 L →ₗ[L] L) (rootVec .G2 L α) = 0 := by
  rw [Finsupp.lapply_apply]
  exact rootVec_apply_inl hα i

private theorem lapply_inr_rootVec {L : Type} [Field L] (β : Fin Tag.G2.rank → ℤ) (hβ : IsRoot .G2 β)
    {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) :
    (Finsupp.lapply (Sum.inr ⟨β, hβ⟩) : RootModule .G2 L →ₗ[L] L) (rootVec .G2 L α)
      = if α = β then 1 else 0 := by
  rw [Finsupp.lapply_apply]
  exact rootVec_apply_inr β hβ hα

private theorem ellH0 {L : Type} [Field L] (s t : Lˣ) :
    (Finsupp.lapply (Sum.inl ia)).comp (xEnd s t) =
      Finsupp.lapply (Sum.inl ia) + (3 : L) • Finsupp.lapply (Sum.inl ir) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rcases b with j | ⟨α, hα⟩
  · rw [show Finsupp.single (Sum.inl j) 1 = hVec .G2 L j from rfl]
    have hj : j = ia ∨ j = ir := by fin_cases j <;> simp [ia, ir]
    rcases hj with rfl | rfl
    · rw [xEnd_hVec_ia]
      simp only [map_sub]
      simp [hVec, ia_ne_ir, ir_ne_ia]
    · rw [xEnd_hVec_ir]
      simp only [map_sub, map_smul]
      simp [hVec, ia_ne_ir]
  · rw [single_inr_eq_rootVec hα]
    obtain ⟨d, -, hd, hσ⟩ := xEnd_rootVec (L := L) s t hα
    rw [LinearMap.add_apply, LinearMap.smul_apply, hd, map_smul,
      lapply_inl_rootVec ia hσ, lapply_inl_rootVec ia hα, lapply_inl_rootVec ir hα]
    simp

private theorem ellH1 {L : Type} [Field L] (s t : Lˣ) :
    (Finsupp.lapply (Sum.inl ir)).comp (xEnd s t) =
      -(Finsupp.lapply (Sum.inl ia)) - (2 : L) • Finsupp.lapply (Sum.inl ir) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rcases b with j | ⟨α, hα⟩
  · rw [show Finsupp.single (Sum.inl j) 1 = hVec .G2 L j from rfl]
    have hj : j = ia ∨ j = ir := by fin_cases j <;> simp [ia, ir]
    rcases hj with rfl | rfl
    · rw [xEnd_hVec_ia]
      simp only [map_sub]
      simp [hVec, ir_ne_ia]
    · rw [xEnd_hVec_ir]
      simp only [map_sub, map_smul]
      simp [hVec, ia_ne_ir, ir_ne_ia]
  · rw [single_inr_eq_rootVec hα]
    obtain ⟨d, -, hd, hσ⟩ := xEnd_rootVec (L := L) s t hα
    rw [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.smul_apply, hd, map_smul,
      lapply_inl_rootVec ir hσ, lapply_inl_rootVec ia hα, lapply_inl_rootVec ir hα]
    simp

private theorem ellRoot {L : Type} [Field L]
    (s t : Lˣ) {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α)
    {hσ : IsRoot .G2 (sigma α)} (d : L)
    (hd : xEnd s t (rootVec .G2 L α) = d • rootVec .G2 L (sigma α)) :
    (Finsupp.lapply (Sum.inr ⟨sigma α, hσ⟩)).comp (xEnd s t) =
      d • Finsupp.lapply (Sum.inr ⟨α, hα⟩) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rcases b with j | ⟨γ, hγ⟩
  · rw [show Finsupp.single (Sum.inl j) 1 = hVec .G2 L j from rfl]
    have hj : j = ia ∨ j = ir := by fin_cases j <;> simp [ia, ir]
    rcases hj with rfl | rfl
    · rw [xEnd_hVec_ia]
      simp only [map_sub]
      simp [hVec]
    · rw [xEnd_hVec_ir]
      simp only [map_sub, map_smul]
      simp [hVec]
  · rw [single_inr_eq_rootVec hγ]
    by_cases hγα : γ = α
    · rw [hγα]
      rw [hd, map_smul, LinearMap.smul_apply, lapply_inr_rootVec (sigma α) hσ hσ,
        lapply_inr_rootVec α hα hα]
      simp
    · obtain ⟨dγ, -, hdγ, hσγ⟩ := xEnd_rootVec (L := L) s t hγ
      have hne : sigma γ ≠ sigma α := fun h => hγα (sigma_injective h)
      rw [hdγ, map_smul, LinearMap.smul_apply, lapply_inr_rootVec (sigma α) hσ hσγ,
        lapply_inr_rootVec α hα hγ]
      simp [hne, hγα]

private theorem rep_isRoot (i : Fin 4) :
    IsRoot .G2 (rep i) := by
  rw [← mem_rootFinset]
  fin_cases i <;> decide +kernel

private noncomputable def rl (α : Fin Tag.G2.rank → ℤ) : Label .G2 := by
  classical
  exact if h : IsRoot .G2 α then Sum.inr ⟨α, h⟩ else Sum.inl ia

private theorem rl_of_isRoot {α : Fin Tag.G2.rank → ℤ}
    (h : IsRoot .G2 α) : rl α = Sum.inr ⟨α, h⟩ := by
  unfold rl
  rw [dif_pos h]

private theorem isRoot_sigma {α : Fin Tag.G2.rank → ℤ}
    (hα : IsRoot .G2 α) : IsRoot .G2 (sigma α) :=
  IsRoot.reflect ia (IsRoot.reflect ir (IsRoot.reflect ia (IsRoot.reflect ir hα)))

private theorem coord_ir {L : Type} [Field L]
    (s t : Lˣ) (h3 : (3 : L) ≠ 0) {v : RootModule .G2 L} (hv : xEnd s t v = v) :
    v (Sum.inl ir) = 0 := by
  have h0 := congrArg (fun w : RootModule .G2 L =>
    ((Finsupp.lapply (Sum.inl ia) : RootModule .G2 L →ₗ[L] L)) w) hv
  simp only [← LinearMap.comp_apply, ellH0, LinearMap.add_apply, LinearMap.smul_apply,
    Finsupp.lapply_apply, smul_eq_mul] at h0
  have h3B : (3 : L) * v (Sum.inl ir) = 0 := by
    have h' := congrArg (fun x : L => x - v (Sum.inl ia)) h0
    simpa using h'.symm
  exact (mul_eq_zero.mp h3B).resolve_left h3

private theorem coord_ia {L : Type} [Field L]
    (s t : Lˣ) (h3 : (3 : L) ≠ 0) {v : RootModule .G2 L} (hv : xEnd s t v = v) :
    v (Sum.inl ia) = 0 := by
  have hir := coord_ir (L := L) s t h3 hv
  have h1 := congrArg (fun w : RootModule .G2 L =>
    ((Finsupp.lapply (Sum.inl ir) : RootModule .G2 L →ₗ[L] L)) w) hv
  simp only [← LinearMap.comp_apply, ellH1, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.smul_apply, Finsupp.lapply_apply, smul_eq_mul] at h1
  rw [hir] at h1
  have : -v (Sum.inl ia) = 0 := by simpa using h1.symm
  exact neg_eq_zero.mp this

private theorem coord_sigma_eq {L : Type} [Field L]
    (s t : Lˣ) {v : RootModule .G2 L} (hv : xEnd s t v = v)
    {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) {hσ : IsRoot .G2 (sigma α)} (d : L)
    (hd : xEnd s t (rootVec .G2 L α) = d • rootVec .G2 L (sigma α)) :
    v (rl (sigma α)) = d * v (rl α) := by
  have h := LinearMap.congr_fun (ellRoot (L := L) (hσ := hσ) s t hα d hd) v
  rw [LinearMap.comp_apply, hv, LinearMap.smul_apply, Finsupp.lapply_apply,
    Finsupp.lapply_apply, smul_eq_mul] at h
  simpa only [rl_of_isRoot hσ, rl_of_isRoot hα] using h

private theorem coord_step {L : Type} [Field L]
    (s t : Lˣ) {v : RootModule .G2 L} (hv : xEnd s t v = v)
    {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) :
    ∃ d : L, d ≠ 0 ∧ v (rl (sigma α)) = d * v (rl α) := by
  obtain ⟨d, hdne, hd, hσ⟩ := xEnd_rootVec (L := L) s t hα
  exact ⟨d, hdne, coord_sigma_eq (L := L) (hσ := hσ) s t hv hα d hd⟩

private theorem coord_zero_of_iterate {L : Type} [Field L]
    (s t : Lˣ) {v : RootModule .G2 L} (hv : xEnd s t v = v)
    (hrep : ∀ i : Fin 4, v (rl (rep i)) = 0) :
    ∀ (m : ℕ) (α : Fin Tag.G2.rank → ℤ) (_hα : IsRoot .G2 α) (i : Fin 4),
      sigma^[m] α = rep i → v (rl α) = 0 := by
  intro m
  induction m with
  | zero =>
    intro α hα i hi
    have hi' : α = rep i := by simpa [Function.iterate_zero_apply] using hi
    rw [hi']
    exact hrep i
  | succ m ih =>
    intro α hα i hi
    obtain ⟨d, hdne, hstep⟩ := coord_step (L := L) s t hv hα
    have hi' : sigma^[m] (sigma α) = rep i := by
      simpa [Function.iterate_succ_apply] using hi
    have hzero : v (rl (sigma α)) = 0 := ih (sigma α) (isRoot_sigma hα) i hi'
    rw [hzero] at hstep
    exact (mul_eq_zero.mp hstep.symm).resolve_left hdne

private theorem root_zero {L : Type} [Field L]
    (s t : Lˣ) {v : RootModule .G2 L} (hv : xEnd s t v = v)
    (hrep : ∀ i : Fin 4, v (rl (rep i)) = 0) {α : Fin Tag.G2.rank → ℤ}
    (hα : IsRoot .G2 α) : v (rl α) = 0 := by
  have H := coord_zero_of_iterate (L := L) s t hv hrep
  have h1 : ∀ β : Fin Tag.G2.rank → ℤ, sigma^[1] β = sigma β := fun β => by
    rw [Function.iterate_succ_apply, Function.iterate_zero_apply]
  have h2 : sigma^[2] α = sigma (sigma α) := by
    rw [Function.iterate_succ_apply, h1]
  rcases root_orbit α hα with h | h | h | h | h | h | h | h | h | h | h | h
  · exact H 0 α hα 0 (by simpa [Function.iterate_zero_apply] using h)
  · exact H 1 α hα 0 (by rw [h1]; exact h)
  · exact H 2 α hα 0 (by rw [h2]; exact h)
  · exact H 0 α hα 1 (by simpa [Function.iterate_zero_apply] using h)
  · exact H 1 α hα 1 (by rw [h1]; exact h)
  · exact H 2 α hα 1 (by rw [h2]; exact h)
  · exact H 0 α hα 2 (by simpa [Function.iterate_zero_apply] using h)
  · exact H 1 α hα 2 (by rw [h1]; exact h)
  · exact H 2 α hα 2 (by rw [h2]; exact h)
  · exact H 0 α hα 3 (by simpa [Function.iterate_zero_apply] using h)
  · exact H 1 α hα 3 (by rw [h1]; exact h)
  · exact H 2 α hα 3 (by rw [h2]; exact h)

private theorem eq_zero_of_fixed {L : Type} [Field L]
    (s t : Lˣ) (h3 : (3 : L) ≠ 0) {v : RootModule .G2 L} (hv : xEnd s t v = v)
    (hrep : ∀ i : Fin 4, v (rl (rep i)) = 0) : v = 0 := by
  apply Finsupp.ext
  intro b
  rcases b with j | ⟨α, hα⟩
  · have hj : j = ia ∨ j = ir := by fin_cases j <;> simp [ia, ir]
    rcases hj with rfl | rfl
    · exact coord_ia (L := L) s t h3 hv
    · exact coord_ir (L := L) s t h3 hv
  · have h := root_zero (L := L) s t hv hrep hα
    rwa [rl_of_isRoot hα] at h

private noncomputable def Phi {L : Type} [Field L]
    (s t : Lˣ) :
    (LinearMap.ker (xEnd s t - 1)) →ₗ[L] (Fin 4 → L) :=
  LinearMap.pi fun i =>
    (Finsupp.lapply (Sum.inr ⟨rep i, rep_isRoot i⟩)).comp
      (LinearMap.ker (xEnd s t - 1)).subtype

private theorem Phi_injective {L : Type} [Field L]
    (s t : Lˣ) (h3 : (3 : L) ≠ 0) : Function.Injective (Phi (L := L) s t) := by
  intro u w h
  apply Subtype.ext
  have hu : xEnd s t (u : RootModule .G2 L) = (u : RootModule .G2 L) := by
    have := u.2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  have hw : xEnd s t (w : RootModule .G2 L) = (w : RootModule .G2 L) := by
    have := w.2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  have hvw : xEnd s t ((u : RootModule .G2 L) - (w : RootModule .G2 L)) =
      (u : RootModule .G2 L) - (w : RootModule .G2 L) := by
    rw [map_sub, hu, hw]
  have hrep : ∀ i : Fin 4,
      ((u : RootModule .G2 L) - (w : RootModule .G2 L)) (rl (rep i)) = 0 := by
    intro i
    have hui : (u : RootModule .G2 L) (Sum.inr ⟨rep i, rep_isRoot i⟩) =
        (w : RootModule .G2 L) (Sum.inr ⟨rep i, rep_isRoot i⟩) := congrFun h i
    rw [rl_of_isRoot (rep_isRoot i), Finsupp.sub_apply, hui, sub_self]
  have hzero := eq_zero_of_fixed (L := L) s t h3 hvw hrep
  rwa [sub_eq_zero] at hzero

private theorem finrank_ker_xEnd_le_four {L : Type} [Field L]
    (s t : Lˣ) (h3 : (3 : L) ≠ 0) :
    Module.finrank L (LinearMap.ker (xEnd s t - 1)) ≤ 4 := by
  have hinj := Phi_injective (L := L) s t h3
  have hle := LinearMap.finrank_le_finrank_of_injective (f := Phi (L := L) s t) hinj
  rwa [Module.finrank_fin_fun] at hle

private theorem fixDim_tz_mul_yq_le_four {L : Type} [Field L]
    (h3 : (3 : L) ≠ 0) (s t : Lˣ) :
    g2AdjFixDim ((tz s t : ModGL .G2 L) * (yq : ModGL .G2 L)) ≤ 4 := by
  unfold g2AdjFixDim
  change Module.finrank L (LinearMap.ker (xEnd s t - 1)) ≤ 4
  exact finrank_ker_xEnd_le_four (L := L) s t h3

private theorem fixDim_tz_mul_yq_sq_le_four {L : Type} [Field L]
    (h3 : (3 : L) ≠ 0) (s t : Lˣ) :
    g2AdjFixDim ((tz s t : ModGL .G2 L) * (yq : ModGL .G2 L) ^ 2) ≤ 4 := by
  have hinv := g2AdjFixDim_inv ((tz s t : ModGL .G2 L) * (yq : ModGL .G2 L) ^ 2)
  rw [← hinv]
  let s' : Lˣ := s⁻¹ * ((t⁻¹) ^ (3 : ℕ))⁻¹
  let t' : Lˣ := s⁻¹ * ((t⁻¹) ^ (2 : ℕ))⁻¹
  have h2 : ((yq : ModGL .G2 L) ^ 2)⁻¹ = (yq : ModGL .G2 L) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ, yq_pow_three]
  have hy : (yq : ModGL .G2 L) * (tz s⁻¹ t⁻¹ : ModGL .G2 L) =
      (tz s' t' : ModGL .G2 L) * yq := by
    have h := yq_tz (K := L) s⁻¹ t⁻¹
    rw [show (tz s' t' : ModGL .G2 L) =
      tz (s⁻¹ * ((t⁻¹) ^ (3 : ℕ))⁻¹) (s⁻¹ * ((t⁻¹) ^ (2 : ℕ))⁻¹) from rfl, ← h]
    group
  have ha : (((tz s t : ModGL .G2 L) * (yq : ModGL .G2 L) ^ 2)⁻¹ : ModGL .G2 L) =
      (tz s' t' : ModGL .G2 L) * (yq : ModGL .G2 L) := by
    rw [mul_inv_rev, h2, tz_inv, hy]
  rw [ha]
  exact fixDim_tz_mul_yq_le_four (L := L) h3 s' t'

theorem g2AdjFixDim_tz_mul_yq_pow_le_four
    {L : Type} [Field L] (h3 : (3 : L) ≠ 0) (s t : Lˣ) {k : ℕ} (hk0 : k ≠ 0) (hk : k < 3) :
    g2AdjFixDim ((tz s t : ModGL .G2 L) * (yq : ModGL .G2 L) ^ k) ≤ 4 := by
  have hk1 : 0 < k := Nat.pos_of_ne_zero hk0
  interval_cases k
  · simpa using fixDim_tz_mul_yq_le_four (L := L) h3 s t
  · simpa using fixDim_tz_mul_yq_sq_le_four (L := L) h3 s t

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
