module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Nat
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

open Matrix
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {W : Type} [CommGroup W]

noncomputable def glPull (e : W ≃* Multiplicative (ι → K)) : GL ι K →* MulAut W :=
  (MulAut.congr e).symm.toMonoidHom.comp (s16gNatHom ι K)

theorem congr_glPull (e : W ≃* Multiplicative (ι → K)) (A : GL ι K) :
    MulAut.congr e (glPull e A) = s16gNatHom ι K A := by
  change MulAut.congr e ((MulAut.congr e).symm (s16gNatHom ι K A)) = s16gNatHom ι K A
  exact MulEquiv.apply_symm_apply _ _

theorem toAdd_glPull_apply (e : W ≃* Multiplicative (ι → K)) (A : GL ι K) (w : W) :
    Multiplicative.toAdd (e (glPull e A w)) = (A : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e w) := by
  change Multiplicative.toAdd
    (e ((MulAut.congr e).symm (s16gNatHom ι K A) w)) = _
  rw [MulAut.congr_symm_apply]
  simp [MulEquiv.trans_apply, s16gNatHom_apply]

theorem glPull_injective (e : W ≃* Multiplicative (ι → K)) : Function.Injective (glPull e) := by
  have h : glPull e
      = (MulAut.congr e).symm.toMonoidHom.comp (s16gNatHom ι K) := rfl
  rw [h]
  exact (MulAut.congr e).symm.injective.comp s16gNatHom_injective

theorem eq_map_glPull_iff (e : W ≃* Multiplicative (ι → K)) {X : Subgroup (MulAut W)}
    {Y : Subgroup (GL ι K)} :
    X.map (MulAut.congr e).toMonoidHom = Y.map (s16gNatHom ι K) ↔ X = Y.map (glPull e) := by
  have hΦ : (MulAut.congr e).symm.toMonoidHom.comp (MulAut.congr e).toMonoidHom
      = MonoidHom.id (MulAut W) :=
    MonoidHom.ext fun x => (MulAut.congr e).symm_apply_apply x
  have hΨ : (MulAut.congr e).toMonoidHom.comp (MulAut.congr e).symm.toMonoidHom
      = MonoidHom.id (MulAut (Multiplicative (ι → K))) :=
    MonoidHom.ext fun x => (MulAut.congr e).apply_symm_apply x
  constructor
  · intro h
    have h' := congrArg (fun Z : Subgroup (MulAut (Multiplicative (ι → K))) =>
      Z.map (MulAut.congr e).symm.toMonoidHom) h
    rw [Subgroup.map_map, Subgroup.map_map, hΦ, Subgroup.map_id] at h'
    show X = Subgroup.map ((MulAut.congr e).symm.toMonoidHom.comp (s16gNatHom ι K)) Y
    exact h'
  · intro h
    rw [h, Subgroup.map_map]
    have h3 : (MulAut.congr e).toMonoidHom.comp (glPull e) = s16gNatHom ι K := by
      rw [glPull, ← MonoidHom.comp_assoc, hΨ, MonoidHom.id_comp]
    rw [h3]

theorem exists_eq_map_glPull_of_le (e : W ≃* Multiplicative (ι → K)) {X : Subgroup (MulAut W)}
    {Y : Subgroup (GL ι K)} (hX : X ≤ Y.map (glPull e)) :
    ∃ X' : Subgroup (GL ι K), X' ≤ Y ∧ X = X'.map (glPull e) := by
  refine ⟨X.comap (glPull e), fun g hg => ?_, ?_⟩
  · exact (Subgroup.mem_map_iff_mem (glPull_injective e)).1 (hX hg)
  · exact (Subgroup.map_comap_eq_self (hX.trans (Subgroup.map_le_range (glPull e) Y))).symm

theorem card_fixV_map_glPull (e : W ≃* Multiplicative (ι → K)) (Y : Subgroup (GL ι K)) :
    Nat.card ↥(CFSG.Quasithin.fixV (Y.map (glPull e))) =
      Nat.card {v : ι → K // ∀ g ∈ Y, (g : Matrix ι ι K) *ᵥ v = v} := by
  classical
  have hfixiff : ∀ w : W, w ∈ CFSG.Quasithin.fixV (Y.map (glPull e)) ↔
      ∀ g ∈ Y, (g : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e w) = Multiplicative.toAdd (e w) := by
    intro w
    rw [CFSG.Quasithin.mem_fixV]
    constructor
    · intro hw g hg
      have hmem : glPull e g ∈ Y.map (glPull e) := Subgroup.mem_map_of_mem (glPull e) hg
      have h := congrArg (fun z : W => Multiplicative.toAdd (e z)) (hw (glPull e g) hmem)
      simpa [toAdd_glPull_apply] using h
    · intro hw x hx
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
      apply e.injective
      apply Multiplicative.toAdd.injective
      rw [toAdd_glPull_apply]
      exact hw g hg
  exact Nat.card_congr ((e.toEquiv.trans Multiplicative.toAdd).subtypeEquiv hfixiff)

def linePull (e : W ≃* Multiplicative (ι → K)) (v : ι → K) : Subgroup W where
  carrier := {w | ∃ s : K, Multiplicative.toAdd (e w) = s • v}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro w₁ w₂ ⟨s₁, h₁⟩ ⟨s₂, h₂⟩
    exact ⟨s₁ + s₂, by rw [map_mul, toAdd_mul, h₁, h₂, add_smul]⟩
  inv_mem' := by
    rintro w ⟨s, h⟩
    exact ⟨-s, by rw [map_inv, toAdd_inv, h, neg_smul]⟩

theorem mem_linePull {e : W ≃* Multiplicative (ι → K)} {v : ι → K} {w : W} :
    w ∈ linePull e v ↔ ∃ s : K, Multiplicative.toAdd (e w) = s • v :=
  Iff.rfl

theorem card_linePull (e : W ≃* Multiplicative (ι → K)) {v : ι → K} (hv : v ≠ 0) :
    Nat.card ↥(linePull e v) = Nat.card K := by
  classical
  let f : K → ↥(linePull e v) := fun s =>
    ⟨e.symm (Multiplicative.ofAdd (s • v)), ⟨s, by simp⟩⟩
  have hf_inj : Function.Injective f := by
    intro s t hst
    have h' := congrArg (fun z : W => Multiplicative.toAdd (e z)) (congrArg Subtype.val hst)
    simp only [f, MulEquiv.apply_symm_apply, toAdd_ofAdd] at h'
    have hsub : (s - t) • v = 0 := by
      rw [sub_smul, h', sub_self]
    rcases smul_eq_zero.1 hsub with h0 | h0
    · exact sub_eq_zero.1 h0
    · exact absurd h0 hv
  have hf_surj : Function.Surjective f := by
    rintro ⟨w, s, hs⟩
    refine ⟨s, Subtype.ext ?_⟩
    show e.symm (Multiplicative.ofAdd (s • v)) = w
    rw [← hs]
    simp
  exact Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩).symm

theorem map_glPull_linePull_of_mulVec_eq (e : W ≃* Multiplicative (ι → K)) {A : GL ι K}
    {v : ι → K} (hA : (A : Matrix ι ι K) *ᵥ v = v) :
    (linePull e v).map (glPull e A).toMonoidHom = linePull e v := by
  apply le_antisymm
  · intro w hw
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hw
    obtain ⟨s, hs⟩ := hx
    refine ⟨s, ?_⟩
    change Multiplicative.toAdd (e (glPull e A x)) = s • v
    rw [toAdd_glPull_apply, hs, Matrix.mulVec_smul, hA]
  · intro w hw
    obtain ⟨s, hs⟩ := hw
    have hw' : w ∈ linePull e v := ⟨s, hs⟩
    have hfix : glPull e A w = w := by
      apply e.injective
      apply Multiplicative.toAdd.injective
      rw [toAdd_glPull_apply, hs, Matrix.mulVec_smul, hA]
    rw [← hfix]
    simpa using Subgroup.mem_map_of_mem (glPull e A).toMonoidHom hw'

theorem map_glPull_linePull_ne (e : W ≃* Multiplicative (ι → K)) {A : GL ι K} {v : ι → K}
    (hA : ∀ s : K, (A : Matrix ι ι K) *ᵥ v ≠ s • v) :
    (linePull e v).map (glPull e A).toMonoidHom ≠ linePull e v := by
  have hmem : e.symm (Multiplicative.ofAdd v) ∈ linePull e v := ⟨1, by simp⟩
  intro heq
  rw [← heq] at hmem
  obtain ⟨x, hx, hxw⟩ := Subgroup.mem_map.1 hmem
  obtain ⟨s, hs⟩ := hx
  have h := congrArg (fun z : W => Multiplicative.toAdd (e z)) hxw
  have h' : (A : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e x) = v := by
    have h2 : Multiplicative.toAdd (e (glPull e A x)) = v := by simpa using h
    rwa [toAdd_glPull_apply] at h2
  rw [hs, Matrix.mulVec_smul] at h'
  rcases eq_or_ne s 0 with hs0 | hs0
  · have hv0 : v = 0 := by rw [← h', hs0, zero_smul]
    exact hA 0 (by rw [hv0]; simp)
  · refine hA s⁻¹ ?_
    calc (A : Matrix ι ι K) *ᵥ v
        = s⁻¹ • (s • ((A : Matrix ι ι K) *ᵥ v)) := by
          rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
      _ = s⁻¹ • v := by rw [h']

theorem exists_mulVec_eq_smul_of_map_glPull_linePull (e : W ≃* Multiplicative (ι → K))
    {A : GL ι K} {v : ι → K} (hA : (linePull e v).map (glPull e A).toMonoidHom = linePull e v) :
    ∃ s : K, (A : Matrix ι ι K) *ᵥ v = s • v := by
  have hmem : e.symm (Multiplicative.ofAdd v) ∈ linePull e v := ⟨1, by simp⟩
  rw [← hA] at hmem
  obtain ⟨x, hx, hxw⟩ := Subgroup.mem_map.1 hmem
  obtain ⟨s, hs⟩ := hx
  have h := congrArg (fun z : W => Multiplicative.toAdd (e z)) hxw
  have h' : (A : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e x) = v := by
    have h2 : Multiplicative.toAdd (e (glPull e A x)) = v := by simpa using h
    rwa [toAdd_glPull_apply] at h2
  rw [hs, Matrix.mulVec_smul] at h'
  rcases eq_or_ne s 0 with hs0 | hs0
  · refine ⟨0, ?_⟩
    have hv0 : v = 0 := by rw [← h', hs0, zero_smul]
    rw [hv0]
    simp
  · refine ⟨s⁻¹, ?_⟩
    calc (A : Matrix ι ι K) *ᵥ v
        = s⁻¹ • (s • ((A : Matrix ι ι K) *ᵥ v)) := by
          rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
      _ = s⁻¹ • v := by rw [h']

theorem mulVec_eq_of_forall_mem_linePull (e : W ≃* Multiplicative (ι → K)) {A : GL ι K}
    {v : ι → K} (hA : ∀ w ∈ linePull e v, glPull e A w = w) : (A : Matrix ι ι K) *ᵥ v = v := by
  have hmem : e.symm (Multiplicative.ofAdd v) ∈ linePull e v := ⟨1, by simp⟩
  have h := congrArg (fun z : W => Multiplicative.toAdd (e z)) (hA _ hmem)
  simpa [toAdd_glPull_apply] using h

theorem linePull_le_fixV_map_glPull (e : W ≃* Multiplicative (ι → K)) {Y : Subgroup (GL ι K)}
    {v : ι → K} (hY : ∀ g ∈ Y, (g : Matrix ι ι K) *ᵥ v = v) :
    linePull e v ≤ CFSG.Quasithin.fixV (Y.map (glPull e)) := by
  intro w hw
  rw [CFSG.Quasithin.mem_fixV]
  intro x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨s, hs⟩ := hw
  apply e.injective
  apply Multiplicative.toAdd.injective
  rw [toAdd_glPull_apply, hs, Matrix.mulVec_smul, hY g hg]

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

end
