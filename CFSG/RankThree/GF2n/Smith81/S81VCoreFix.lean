module

public import CFSG.RankThree.GF2n.Smith81.S81VModelRoot
public import CFSG.RankThree.GF2n.Smith81.S81VAmbGen
public import CFSG.RankThree.GF2n.Smith81.S81UTrans

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} {K : Type} [Field K]
  {V : Type} [AddCommGroup V] [Module K V]

@[expose] def fixU (σ : F ≃+* F) (A : SUid σ 6 →* (V ≃ₗ[K] V)) : Submodule K V where
  carrier := {v | ∀ u ∈ PtStab σ (W₀ F), A u v = v}
  add_mem' {v w} hv hw u hu := by rw [map_add, hv u hu, hw u hu]
  zero_mem' u _ := map_zero _
  smul_mem' c v hv u hu := by rw [map_smul, hv u hu]

theorem mem_fixU {A : SUid σ 6 →* (V ≃ₗ[K] V)} {v : V} :
    v ∈ fixU σ A ↔ ∀ u ∈ PtStab σ (W₀ F), A u v = v := Iff.rfl

@[expose] def V1U (σ : F ≃+* F) (A : SUid σ 6 →* (V ≃ₗ[K] V)) (β : V →ₗ[K] V →ₗ[K] K) :
    Submodule K V where
  carrier := {w | (∀ v ∈ fixU σ A, β v w = 0) ∧ ∀ u ∈ PtStab σ (W₀ F), A u w - w ∈ fixU σ A}
  add_mem' {w w'} hw hw' := by
    refine ⟨fun v hv => ?_, fun u hu => ?_⟩
    · rw [map_add, hw.1 v hv, hw'.1 v hv, add_zero]
    · have : A u (w + w') - (w + w') = (A u w - w) + (A u w' - w') := by rw [map_add]; abel
      rw [this]
      exact (fixU σ A).add_mem (hw.2 u hu) (hw'.2 u hu)
  zero_mem' := ⟨fun v _ => by simp, fun u _ => by simp⟩
  smul_mem' c w hw := by
    refine ⟨fun v hv => ?_, fun u hu => ?_⟩
    · rw [map_smul, hw.1 v hv, smul_zero]
    · have : A u (c • w) - c • w = c • (A u w - w) := by rw [map_smul, smul_sub]
      rw [this]
      exact (fixU σ A).smul_mem c (hw.2 u hu)

theorem mem_V1U {A : SUid σ 6 →* (V ≃ₗ[K] V)} {β : V →ₗ[K] V →ₗ[K] K} {w : V} :
    w ∈ V1U σ A β ↔ (∀ v ∈ fixU σ A, β v w = 0) ∧ ∀ u ∈ PtStab σ (W₀ F), A u w - w ∈ fixU σ A :=
  Iff.rfl

@[expose] def fixAt (σ : F ≃+* F) (A : SUid σ 6 →* (V ≃ₗ[K] V)) (W : Submodule F (Fin 6 → F)) :
    Submodule K V where
  carrier := {v | ∀ u ∈ PtStab σ W, A u v = v}
  add_mem' {v w} hv hw u hu := by rw [map_add, hv u hu, hw u hu]
  zero_mem' u _ := map_zero _
  smul_mem' c v hv u hu := by rw [map_smul, hv u hu]

theorem mem_fixAt {A : SUid σ 6 →* (V ≃ₗ[K] V)} {W : Submodule F (Fin 6 → F)} {v : V} :
    v ∈ fixAt σ A W ↔ ∀ u ∈ PtStab σ W, A u v = v := Iff.rfl

@[expose] def V1At (σ : F ≃+* F) (A : SUid σ 6 →* (V ≃ₗ[K] V)) (β : V →ₗ[K] V →ₗ[K] K)
    (W : Submodule F (Fin 6 → F)) : Submodule K V where
  carrier := {w | (∀ v ∈ fixAt σ A W, β v w = 0) ∧ ∀ u ∈ PtStab σ W, A u w - w ∈ fixAt σ A W}
  add_mem' {w w'} hw hw' := by
    refine ⟨fun v hv => ?_, fun u hu => ?_⟩
    · rw [map_add, hw.1 v hv, hw'.1 v hv, add_zero]
    · have : A u (w + w') - (w + w') = (A u w - w) + (A u w' - w') := by rw [map_add]; abel
      rw [this]
      exact (fixAt σ A W).add_mem (hw.2 u hu) (hw'.2 u hu)
  zero_mem' := ⟨fun v _ => by simp, fun u _ => by simp⟩
  smul_mem' c w hw := by
    refine ⟨fun v hv => ?_, fun u hu => ?_⟩
    · rw [map_smul, hw.1 v hv, smul_zero]
    · have : A u (c • w) - c • w = c • (A u w - w) := by rw [map_smul, smul_sub]
      rw [this]
      exact (fixAt σ A W).smul_mem c (hw.2 u hu)

theorem mem_V1At {A : SUid σ 6 →* (V ≃ₗ[K] V)} {β : V →ₗ[K] V →ₗ[K] K} {W : Submodule F (Fin 6 → F)}
    {w : V} : w ∈ V1At σ A β W ↔
      (∀ v ∈ fixAt σ A W, β v w = 0) ∧ ∀ u ∈ PtStab σ W, A u w - w ∈ fixAt σ A W := Iff.rfl

theorem exists_frame_T0 (hσ : IsUnitaryInvolution σ) : ∃ b : Fin 3 → Fin 6 → F, Frame σ e3uT0Vec b := by
  have hv : exteriorPower.ιMulti F 3 (e3uT0Vec (F := F)) ≠ 0 := by
    rw [← pt0_eq_ιMulti_T0]
    exact pt0_ne_zero
  have hiso : ∀ i j : Fin 3,
      ∑ k : Fin 6, σ (e3uT0Vec (F := F) i k) * e3uT0Vec (F := F) j k = 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [e3uT0Vec, Fin.sum_univ_six, CharTwo.add_self_eq_zero]
  obtain ⟨b, hab, hbb⟩ := exists_hyperbolic_partners hσ hv hiso
  exact ⟨b, fun i j => hiso i j, fun i j => hbb i j, fun i j => hab i j⟩

private theorem conj_mem_PtStab_aux {g u : SUid σ 6} (hg : g ∈ Pstab σ (W₀ F))
    (hu : u ∈ PtStab σ (W₀ F)) : g⁻¹ * u * g ∈ PtStab σ (W₀ F) := by
  have hg' : (W₀ F).map (gLin g) = W₀ F := hg
  rw [mem_ptStab]
  intro w hw
  have hgw : g • w ∈ W₀ F := by
    have h1 : gLin g w ∈ (W₀ F).map (gLin g) := Submodule.mem_map_of_mem hw
    rw [hg'] at h1
    exact h1
  rw [mul_smul, mul_smul, hu (g • w) hgw, inv_smul_smul]

private def lineStab (A : SUid σ 6 →* (V ≃ₗ[K] V)) (L : Submodule K V) : Subgroup (SUid σ 6) where
  carrier := {g | (∀ x ∈ L, A g x ∈ L) ∧ ∀ x ∈ L, A g⁻¹ x ∈ L}
  mul_mem' {g h} hg hh := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [map_mul, LinearEquiv.mul_apply]
      exact hg.1 _ (hh.1 x hx)
    · rw [_root_.mul_inv_rev, map_mul, LinearEquiv.mul_apply]
      exact hh.2 _ (hg.2 x hx)
  one_mem' := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [map_one]
      exact hx
    · rw [inv_one, map_one]
      exact hx
  inv_mem' {g} hg := by
    refine ⟨hg.2, fun x hx => ?_⟩
    rw [inv_inv]
    exact hg.1 x hx

private theorem mem_lineStab {A : SUid σ 6 →* (V ≃ₗ[K] V)} {L : Submodule K V} {g : SUid σ 6} :
    g ∈ lineStab A L ↔ (∀ x ∈ L, A g x ∈ L) ∧ ∀ x ∈ L, A g⁻¹ x ∈ L := Iff.rfl

variable {b : Fin 3 → Fin 6 → F} (hσ : IsUnitaryInvolution σ) (hf : Frame σ e3uT0Vec b) (e₀ : K ≃+* Fσ σ)
  (A : SUid σ 6 →* (V ≃ₗ[K] V))

include hσ hf

theorem toRankOne_fix_eq : ((rootDatumU hσ hf e₀).toRankOne A).fix = fixU σ A := by
  ext v
  rw [RankOneData.mem_fix, mem_fixU]
  constructor
  · intro h u hu
    obtain ⟨H, rfl⟩ := exists_uK_of_mem_PtStab hσ.invol hf (e₀ := e₀) hu
    exact h H
  · intro h H
    exact h _ (uK_mem_PtStab hσ.invol hf H)

theorem toRankOne_V1_eq (β : V →ₗ[K] V →ₗ[K] K) :
    ((rootDatumU hσ hf e₀).toRankOne A).V1 β = V1U σ A β := by
  ext w
  rw [RankOneData.mem_V1, mem_V1U, toRankOne_fix_eq hσ hf e₀ A]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun u hu => ?_⟩
    obtain ⟨H, rfl⟩ := exists_uK_of_mem_PtStab hσ.invol hf (e₀ := e₀) hu
    exact h2 H
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun H => h2 _ (uK_mem_PtStab hσ.invol hf H)⟩

theorem fixU_map_le_of_mem_Pstab {g : SUid σ 6} (hg : g ∈ Pstab σ (W₀ F)) :
    (fixU σ A).map (A g : V →ₗ[K] V) ≤ fixU σ A := by
  rintro _ ⟨v, hv, rfl⟩
  rw [mem_fixU]
  intro u hu
  have hc : g⁻¹ * u * g ∈ PtStab σ (W₀ F) := conj_mem_PtStab_aux hg hu
  have hfix : A (g⁻¹ * u * g) v = v := mem_fixU.1 hv _ hc
  have key : A u * A g = A g * A (g⁻¹ * u * g) := by
    rw [← map_mul, ← map_mul]
    exact congrArg A (by group)
  have h2 : A u (A g v) = A g (A (g⁻¹ * u * g) v) := by
    rw [← LinearEquiv.mul_apply (A u) (A g), ← LinearEquiv.mul_apply (A g) (A (g⁻¹ * u * g)), key]
  show A u (A g v) = A g v
  rw [h2, hfix]

theorem sv_U (hline : finrank K (fixU σ A) = 1)
    (hspan : ⨆ g : SUid σ 6, (fixU σ A).map (A g : V →ₗ[K] V) = ⊤) (hV : 1 < finrank K V)
    {v₀ : V} (hv₀ : v₀ ∈ fixU σ A) (hne : v₀ ≠ 0) : A (sU hσ.invol hf) v₀ ∉ fixU σ A := by
  intro hs
  have hmul : ∀ x ∈ fixU σ A, ∃ c : K, c • v₀ = x := by
    intro x hx
    have hnz : (⟨v₀, hv₀⟩ : ↥(fixU σ A)) ≠ 0 := fun h => hne (congrArg Subtype.val h)
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hline hnz ⟨x, hx⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  have hlin : ∀ g : SUid σ 6, A g v₀ ∈ fixU σ A → ∀ x ∈ fixU σ A, A g x ∈ fixU σ A := by
    intro g hg x hx
    obtain ⟨c, rfl⟩ := hmul x hx
    rw [map_smul]
    exact (fixU σ A).smul_mem c hg
  have hsinv : (sU hσ.invol hf)⁻¹ = sU hσ.invol hf :=
    inv_eq_of_mul_eq_one_right (sU_sq hσ.invol hf)
  have hsStab : sU hσ.invol hf ∈ lineStab A (fixU σ A) := by
    rw [mem_lineStab, hsinv]
    exact ⟨hlin _ hs, hlin _ hs⟩
  have hPle : Pstab σ (W₀ F) ≤ lineStab A (fixU σ A) := by
    intro g hg
    rw [mem_lineStab]
    exact ⟨fun x hx => fixU_map_le_of_mem_Pstab hσ hf A hg (Submodule.mem_map_of_mem hx),
      fun x hx => fixU_map_le_of_mem_Pstab hσ hf A (inv_mem hg) (Submodule.mem_map_of_mem hx)⟩
  have hTop : lineStab A (fixU σ A) = ⊤ := closure_eq_top hσ hf _ hPle hsStab
  have hall : ∀ g : SUid σ 6, ∀ x ∈ fixU σ A, A g x ∈ fixU σ A := by
    intro g
    have hg : g ∈ lineStab A (fixU σ A) := by
      rw [hTop]
      exact Subgroup.mem_top g
    exact (mem_lineStab.1 hg).1
  have hle : (⨆ g : SUid σ 6, (fixU σ A).map (A g : V →ₗ[K] V)) ≤ fixU σ A := by
    refine iSup_le fun g => ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hall g x hx
  rw [hspan, top_le_iff] at hle
  rw [hle, finrank_top] at hline
  omega

end CFSG.RankThree.GF2n.Smith81.S81V
