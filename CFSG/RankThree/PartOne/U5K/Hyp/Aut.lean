module

public import CFSG.RankThree.PartOne.U5K.Hyp.Irred
public import CFSG.RankThree.PartOne.U5K.ThompsonMap

public noncomputable section

namespace CFSG.RankThree.PartOne.U5K.Hyp

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

@[expose] def innM : hypSU hK 2 1 →* MulAut (hypPSU hK 2 1) :=
  (MulAut.conj : hypPSU hK 2 1 →* MulAut (hypPSU hK 2 1)).comp (hypProj hK 2 1)

variable {hK}

theorem innM_apply (g : hypSU hK 2 1) (z : hypPSU hK 2 1) :
    innM hK g z = hypProj hK 2 1 g * z * (hypProj hK 2 1 g)⁻¹ := rfl

theorem innM_eq_one_iff (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥) {g : hypSU hK 2 1} :
    innM hK g = 1 ↔ g ∈ hypScalars hK 2 1 := by
  have hk := SetLike.ext_iff.1 (ker_hypProj hK 2 1) g
  constructor
  · intro h
    have hc : hypProj hK 2 1 g ∈ Subgroup.center (hypPSU hK 2 1) := by
      rw [Subgroup.mem_center_iff]
      intro z
      have := congrArg (fun a : MulAut (hypPSU hK 2 1) => a z) h
      simp only [innM_apply, MulAut.one_apply] at this
      calc z * hypProj hK 2 1 g = (hypProj hK 2 1 g * z * (hypProj hK 2 1 g)⁻¹) *
            hypProj hK 2 1 g := by rw [this]
        _ = hypProj hK 2 1 g * z := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hk.1 hc
  · intro h
    have h1 : hypProj hK 2 1 g = 1 := hk.2 h
    ext z
    simp [innM_apply, h1]

theorem Usub_inf_scalars : hypUnitriangular hK 2 1 ⊓ hypScalars hK 2 1 = ⊥ :=
  (unitary_order_and_Sylow hK (r := 2) (ε := 1) (by norm_num) (by norm_num)).2.2.1

theorem innM_injOn (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥) {g g' : hypSU hK 2 1}
    (hg : g ∈ hypUnitriangular hK 2 1) (hg' : g' ∈ hypUnitriangular hK 2 1)
    (h : innM hK g = innM hK g') : g = g' := by
  have h1 : innM hK (g⁻¹ * g') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 := (innM_eq_one_iff hZ).1 h1
  have h3 : g⁻¹ * g' ∈ hypUnitriangular hK 2 1 := mul_mem (inv_mem hg) hg'
  have h4 : g⁻¹ * g' ∈ hypUnitriangular hK 2 1 ⊓ hypScalars hK 2 1 := ⟨h3, h2⟩
  rw [Usub_inf_scalars, Subgroup.mem_bot] at h4
  exact inv_mul_eq_one.1 h4

section Subs

variable (hK)

@[expose] def Uh : Subgroup (MulAut (hypPSU hK 2 1)) := (hypUnitriangular hK 2 1).map (innM hK)

@[expose] def Sh : Subgroup (MulAut (hypPSU hK 2 1)) := (Ssub hK).map (innM hK)

@[expose] def Vh : Subgroup (MulAut (hypPSU hK 2 1)) := (Vsub hK).map (innM hK)

@[expose] def Pi : Subgroup (MulAut (hypPSU hK 2 1)) :=
  (MulAut.conj : hypPSU hK 2 1 →* MulAut (hypPSU hK 2 1)).range

variable {hK}

theorem Sh_le_Uh : Sh hK ≤ Uh hK := Subgroup.map_mono Ssub_le_Usub

theorem Vh_le_Sh : Vh hK ≤ Sh hK := Subgroup.map_mono Vsub_le_Ssub

theorem Uh_le_Pi : Uh hK ≤ Pi hK := by
  rintro _ ⟨g, -, rfl⟩
  exact ⟨hypProj hK 2 1 g, rfl⟩

theorem range_innM : (innM hK).range = Pi hK := by
  ext ρ
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨hypProj hK 2 1 g, rfl⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨g, rfl⟩ := hypProj_surjective hK 2 1 z
    exact ⟨g, rfl⟩

instance Pi_normal : (Pi hK).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨z, rfl⟩ := hn
  refine ⟨g z, ?_⟩
  ext x
  simp [MulAut.conj_apply]

theorem card_map_innM (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥) {X : Subgroup (hypSU hK 2 1)}
    (hX : X ≤ hypUnitriangular hK 2 1) : Nat.card (X.map (innM hK)) = Nat.card X := by
  have hinj : Function.Injective ((innM hK).comp X.subtype) := by
    intro a b hab
    exact Subtype.ext (innM_injOn hZ (hX a.2) (hX b.2) hab)
  exact (Nat.card_congr (equivMapOfInjOn (innM hK) hinj).toEquiv).symm

theorem card_Vh (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥) : Nat.card (Vh hK) = (2 ^ f) ^ 4 := by
  unfold Vh
  rw [card_map_innM hZ ((Vsub_le_Ssub).trans Ssub_le_Usub), card_Vsub]

end Subs

section Fin

variable (hK)

theorem finite_hypSU : Finite (hypSU hK 2 1) := by
  have : Finite K := hK.finite
  infer_instance

theorem finite_hypPSU : Finite (hypPSU hK 2 1) := by
  have := finite_hypSU hK
  infer_instance

theorem finite_mulAut_hyp : Finite (MulAut (hypPSU hK 2 1)) := by
  have := finite_hypPSU hK
  exact Finite.of_injective (fun α : MulAut (hypPSU hK 2 1) => (α : hypPSU hK 2 1 → hypPSU hK 2 1))
    DFunLike.coe_injective

end Fin

section Elem

theorem elemAb_Uh (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥)
    {F : Subgroup (MulAut (hypPSU hK 2 1))} (hF : F ≤ Uh hK)
    (hc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hs : ∀ x ∈ F, x * x = 1) :
    F ≤ Vh hK ∨ Nat.card F ≤ (2 ^ f) ^ 3 := by
  set G : Subgroup (hypSU hK 2 1) := hypUnitriangular hK 2 1 ⊓ F.comap (innM hK) with hG
  have hGU : G ≤ hypUnitriangular hK 2 1 := inf_le_left
  have hmap : G.map (innM hK) = F := by
    ext ρ
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg.2
    · intro hρ
      obtain ⟨g, hg, rfl⟩ := hF hρ
      exact ⟨g, ⟨hg, hρ⟩, rfl⟩
  have hGc : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := by
    intro x hx y hy
    apply innM_injOn hZ (mul_mem (hGU hx) (hGU hy)) (mul_mem (hGU hy) (hGU hx))
    rw [map_mul, map_mul]
    exact hc _ hx.2 _ hy.2
  have hGs : ∀ x ∈ G, x * x = 1 := by
    intro x hx
    apply innM_injOn hZ (mul_mem (hGU hx) (hGU hx)) (one_mem _)
    rw [map_mul, map_one]
    exact hs _ hx.2
  rcases elemAb_le_Vsub_or_card_le hGU hGc hGs with h | h
  · left
    rw [← hmap]
    exact Subgroup.map_mono h
  · right
    rw [← hmap, card_map_innM hZ hGU]
    exact h

theorem Vh_comm {x y : MulAut (hypPSU hK 2 1)} (hx : x ∈ Vh hK) (hy : y ∈ Vh hK) :
    x * y = y * x := by
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨v', hv', rfl⟩ := hy
  rw [← map_mul, ← map_mul, Vsub_comm hv hv']

theorem Vh_sq {x : MulAut (hypPSU hK 2 1)} (hx : x ∈ Vh hK) : x * x = 1 := by
  obtain ⟨v, hv, rfl⟩ := hx
  rw [← map_mul, Vsub_sq hv, map_one]

theorem zOf_Sh (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥) : zOf (Sh hK) = Vh hK := by
  ext ρ
  constructor
  · intro hρ
    obtain ⟨hρS, hρc⟩ := mem_zOf_iff.1 hρ
    obtain ⟨s₀, hs₀, rfl⟩ := hρS
    refine ⟨s₀, (central_Ssub_iff hs₀).1 (fun s hs => ?_), rfl⟩
    have := hρc (innM hK s) ⟨s, hs, rfl⟩
    apply innM_injOn hZ (mul_mem (Ssub_le_Usub hs) (Ssub_le_Usub hs₀))
      (mul_mem (Ssub_le_Usub hs₀) (Ssub_le_Usub hs))
    rw [map_mul, map_mul]
    exact this
  · rintro ⟨v, hv, rfl⟩
    refine mem_zOf_iff.2 ⟨⟨v, Vsub_le_Ssub hv, rfl⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, (central_Ssub_iff (Vsub_le_Ssub hv)).2 hv s hs]

end Elem

section SylowPart

theorem conj_injective (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥) :
    Function.Injective (MulAut.conj : hypPSU hK 2 1 →* MulAut (hypPSU hK 2 1)) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  have hc : z ∈ Subgroup.center (hypPSU hK 2 1) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := congrArg (fun a : MulAut (hypPSU hK 2 1) => a x) hz
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * z = (z * x * z⁻¹) * z := by rw [this]
      _ = z * x := by group
  rw [hZ] at hc
  exact hc

theorem Uh_eq_map : Uh hK = (hypProjUnitriangular hK 2 1).map
    (MulAut.conj : hypPSU hK 2 1 →* MulAut (hypPSU hK 2 1)) := by
  unfold Uh hypProjUnitriangular
  rw [Subgroup.map_map]
  rfl

theorem Pi_eq_map : Pi hK = (⊤ : Subgroup (hypPSU hK 2 1)).map
    (MulAut.conj : hypPSU hK 2 1 →* MulAut (hypPSU hK 2 1)) := by
  rw [Pi, MonoidHom.range_eq_map]

theorem isSylow_Uh (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥) :
    CFSG.ABGLocalTools.IsSylowOf 2 (Uh hK) (Pi hK) := by
  have := finite_mulAut_hyp hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  obtain ⟨hcard, -, -, -, ⟨Q, hQ⟩, -⟩ := unitary_order_and_Sylow hK (r := 2) (ε := 1)
    (by norm_num) (by norm_num)
  refine ⟨Uh_le_Pi, ?_, ?_⟩
  · have h1 : Nat.card (Uh hK) = (2 ^ f) ^ 10 := by
      unfold Uh
      rw [card_map_innM hZ le_rfl, hcard]
    exact IsPGroup.of_card (n := f * 10) (by rw [h1, ← pow_mul])
  · rw [Uh_eq_map, Pi_eq_map, Subgroup.relIndex_map_map_of_injective _ _ (conj_injective hZ),
      Subgroup.relIndex_top_right, ← hQ]
    exact Q.not_dvd_index

end SylowPart

section Normalizer

theorem mem_normalizer_of_conj_le {G : Type*} [Group G] [Finite G] {K : Subgroup G} {g : G}
    (h : ∀ k ∈ K, g * k * g⁻¹ ∈ K) : g ∈ Subgroup.normalizer (K : Set G) := by
  have hinj : Function.Injective (fun k : K => (⟨g * k * g⁻¹, h k k.2⟩ : K)) := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only at this
    exact Subtype.ext (by simpa using this)
  have hsurj := Finite.injective_iff_surjective.1 hinj
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨h n, fun hn => ?_⟩
  obtain ⟨k, hk⟩ := hsurj ⟨g * n * g⁻¹, hn⟩
  have : (k : G) = n := by
    have := congrArg Subtype.val hk
    simpa using this
  rw [← this]
  exact k.2

theorem innM_mem_normalizer_Sh {g : hypSU hK 2 1}
    (hg : ∀ s ∈ Ssub hK, g * s * g⁻¹ ∈ Ssub hK) :
    innM hK g ∈ Subgroup.normalizer (Sh hK : Set (MulAut (hypPSU hK 2 1))) := by
  have := finite_mulAut_hyp hK
  refine mem_normalizer_of_conj_le fun ρ hρ => ?_
  obtain ⟨s, hs, rfl⟩ := hρ
  exact ⟨g * s * g⁻¹, hg s hs, by rw [map_mul, map_mul, map_inv]⟩

theorem innM_lev_mem_normalizer_Sh (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det) :
    innM hK (lev A hA) ∈ Subgroup.normalizer (Sh hK : Set (MulAut (hypPSU hK 2 1))) :=
  innM_mem_normalizer_Sh fun _ hs => lev_conj_mem_Ssub A hA hs

theorem innM_Usub_mem_normalizer_Sh {g : hypSU hK 2 1} (hg : g ∈ hypUnitriangular hK 2 1) :
    innM hK g ∈ Subgroup.normalizer (Sh hK : Set (MulAut (hypPSU hK 2 1))) :=
  innM_mem_normalizer_Sh fun _ hs => conj_mem_Ssub hg hs

theorem mem_normalizer_Vh_of_Sh (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥)
    {ρ : MulAut (hypPSU hK 2 1)}
    (hρS : ρ ∈ Subgroup.normalizer (Sh hK : Set (MulAut (hypPSU hK 2 1)))) :
    ρ ∈ Subgroup.normalizer (Vh hK : Set (MulAut (hypPSU hK 2 1))) := by
  have := finite_mulAut_hyp hK
  refine mem_normalizer_of_conj_le fun v hv => ?_
  have hvS : ρ * v * ρ⁻¹ ∈ Sh hK := (Subgroup.mem_normalizer_iff.1 hρS v).1 (Vh_le_Sh hv)
  rw [← zOf_Sh hZ]
  refine mem_zOf_iff.2 ⟨hvS, fun s hs => ?_⟩
  have hs' : ρ⁻¹ * s * ρ ∈ Sh hK := by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hρS) s).1 hs
    simpa using this
  have hvc := (mem_zOf_iff.1 (by rw [zOf_Sh hZ]; exact hv)).2 _ hs'
  calc s * (ρ * v * ρ⁻¹) = ρ * ((ρ⁻¹ * s * ρ) * v) * ρ⁻¹ := by group
    _ = ρ * (v * (ρ⁻¹ * s * ρ)) * ρ⁻¹ := by rw [hvc]
    _ = (ρ * v * ρ⁻¹) * s := by group

end Normalizer

section Core

@[expose] def swapM : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

theorem isUnit_det_swapM : IsUnit (swapM : Matrix (Fin 2) (Fin 2) K).det := by
  simp [swapM, Matrix.det_fin_two]

theorem swapM_mul_swapM : (swapM : Matrix (Fin 2) (Fin 2) K) * swapM = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapM, Matrix.mul_apply, Fin.sum_univ_two]

theorem swap_conj_entry {u : hypSU hK 2 1} (hu : u ∈ hypUnitriangular hK 2 1) :
    mat (lev swapM isUnit_det_swapM * u * (lev swapM isUnit_det_swapM)⁻¹) (.inl 1) (.inl 0) =
      aOf u := by
  obtain ⟨a, x, C, -, hu'⟩ := exists_coord hu
  have haOf := aOf_eq_of_coord hu'
  set l : hypSU hK 2 1 := lev swapM isUnit_det_swapM with hl
  set d : K := hK.bar (swapM : Matrix (Fin 2) (Fin 2) K).det /
    (swapM : Matrix (Fin 2) (Fin 2) K).det with hd
  have hdd : hK.bar d * d = 1 := bar_mul_self_of_eq_div isUnit_det_swapM rfl
  have hA : IsUnit (swapM : Matrix (Fin 2) (Fin 2) K).det := isUnit_det_swapM
  have hPAP : swapM * !![1, a; 0, 1] * swapM = (!![1, 0; a, 1] : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [swapM, Matrix.mul_apply, Fin.sum_univ_two]
  have h1 : mat l * mat u = (oddDiag hK (swapM * !![1, a; 0, 1] * swapM) 1 *
      oddUni hK (d⁻¹ • (swapM *ᵥ x)) (swapM * C * (swapM.map hK.bar)ᵀ)) * mat l := by
    rw [hl, mat_lev, hu', ← Matrix.mul_assoc, oddDiag_mul, mul_one]
    have h2 : oddDiag hK (swapM * !![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) K) d =
        oddDiag hK (swapM * !![1, a; 0, 1] * swapM) 1 * oddDiag hK swapM d := by
      rw [oddDiag_mul, one_mul, Matrix.mul_assoc, swapM_mul_swapM, Matrix.mul_one]
    rw [h2, Matrix.mul_assoc, oddDiag_mul_oddUni_comm hK hA hdd, ← Matrix.mul_assoc]
  have h3 : mat l * mat l⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
  have h4 : mat (l * u * l⁻¹) = oddDiag hK (swapM * !![1, a; 0, 1] * swapM) 1 *
      oddUni hK (d⁻¹ • (swapM *ᵥ x)) (swapM * C * (swapM.map hK.bar)ᵀ) := by
    rw [mat_mul, mat_mul, h1, Matrix.mul_assoc, h3, Matrix.mul_one]
  rw [h4, oddDiag_mul_oddUni, hPAP, haOf]
  simp

theorem core_inner (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥)
    {R : Subgroup (MulAut (hypPSU hK 2 1))} (hR : R ≤ Pi hK) (hR2 : IsPGroup 2 R)
    (hN : ∀ ρ ∈ Pi hK, ρ ∈ Subgroup.normalizer (Sh hK : Set (MulAut (hypPSU hK 2 1))) →
      ρ ∈ Subgroup.normalizer (R : Set (MulAut (hypPSU hK 2 1)))) : R ≤ Sh hK := by
  have := finite_mulAut_hyp hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUhN : Uh hK ≤ Subgroup.normalizer (R : Set (MulAut (hypPSU hK 2 1))) := by
    intro ρ hρ
    obtain ⟨g, hg, rfl⟩ := hρ
    exact hN _ (Uh_le_Pi ⟨g, hg, rfl⟩) (innM_Usub_mem_normalizer_Sh hg)
  have hsup : IsPGroup 2 ↥(Uh hK ⊔ R) :=
    (CFSG.ABGLocalTools.IsSylowOf.isPGroup (isSylow_Uh hZ)).to_sup_of_normal_right' hR2 hUhN
  have hRUh : R ≤ Uh hK := by
    have := (isSylow_Uh hZ).eq_of_le (le_sup_left : Uh hK ≤ Uh hK ⊔ R)
      (sup_le Uh_le_Pi hR) hsup
    exact le_sup_right.trans this.le
  set l : hypSU hK 2 1 := lev swapM isUnit_det_swapM with hl
  have hlR : innM hK l ∈ Subgroup.normalizer (R : Set (MulAut (hypPSU hK 2 1))) :=
    hN _ (range_innM (hK := hK) ▸ ⟨l, rfl⟩) (innM_lev_mem_normalizer_Sh _ _)
  intro ρ hρ
  obtain ⟨u, hu, rfl⟩ := hRUh hρ
  have hmem : innM hK l * innM hK u * (innM hK l)⁻¹ ∈ R :=
    ((Subgroup.mem_normalizer_iff.1 hlR) _).1 hρ
  obtain ⟨u', hu', hu'e⟩ := hRUh hmem
  have h1 : innM hK (u'⁻¹ * (l * u * l⁻¹)) = 1 := by
    rw [map_mul, map_inv, hu'e, map_mul, map_mul, map_inv, inv_mul_cancel]
  obtain ⟨c, -, -, hc⟩ := (innM_eq_one_iff hZ).1 h1
  have h2 : l * u * l⁻¹ = u' * (u'⁻¹ * (l * u * l⁻¹)) := by group
  have h3 : mat (l * u * l⁻¹) (.inl 1) (.inl 0) = 0 := by
    rw [h2, mat_mul]
    have hz : mat (u'⁻¹ * (l * u * l⁻¹)) = Matrix.scalar _ (c : K) := by
      change ((u'⁻¹ * (l * u * l⁻¹) : hypSU hK 2 1) : GL (HypIndex 2 1) K).1 = _
      rw [hc]
      rfl
    rw [hz]
    simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
      U_lower hu' (a := .inl 1) (b := .inl 0) (by simp)]
  rw [swap_conj_entry hu] at h3
  exact ⟨u, (mem_Ssub_iff hu).2 h3, rfl⟩

end Core

end CFSG.RankThree.PartOne.U5K.Hyp
