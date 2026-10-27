module

public import CFSG.LocalAnalysis.StandardType.GGDepED4LowDefs
public import CFSG.LocalAnalysis.StandardType.GGDepEModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nLM_ELα_castSucc (i : Fin 6) (k : Fin 5) :
    ggDepELα i k.castSucc = (((CartanMatrix.E 6) i k.castSucc : ℤ) : ZMod 3) := by
  rw [CartanMatrix.E_six_eq]
  fin_cases i <;> fin_cases k <;> decide +kernel

private lemma l05nLM_ELα_last (i : Fin 6) : ggDepELα i (Fin.last 5) = 0 := by
  fin_cases i <;> decide +kernel

private noncomputable def l05nLMψ {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 6 → V) (x : V) : (Fin 6 → ZMod 3) →ₗ[ZMod 3] V :=
  ∑ k : Fin 6, (LinearMap.proj k).smulRight
    (if hk : k.val < 5 then h k else x)

private lemma l05nLMψ_apply {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 6 → V) (x : V) (w : Fin 6 → ZMod 3) :
    l05nLMψ h x w = ∑ k : Fin 6, w k •
      (if hk : k.val < 5 then h k else x) := by
  simp [l05nLMψ, Finset.sum_apply, LinearMap.smulRight_apply]

private lemma l05nLMψ_single {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 6 → V) (x : V) (k : Fin 6) :
    l05nLMψ h x (Pi.single k (1 : ZMod 3)) =
      (if hk : k.val < 5 then h k else x) := by
  rw [l05nLMψ_apply, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_smul]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

private lemma l05nLMψ_ker {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Fin 6 → V} {x : V}
    (hxnot : x ∉ Submodule.span (ZMod 3) (Set.range h))
    (hli : LinearIndependent (ZMod 3) (fun k : Fin 5 => h k.castSucc))
    (w : Fin 6 → ZMod 3) (hw : l05nLMψ h x w = 0) : w = 0 := by
  have hsum : (∑ k : Fin 5, w k.castSucc • h k.castSucc) + w (Fin.last 5) • x = 0 := by
    rw [l05nLMψ_apply] at hw
    rw [Fin.sum_univ_castSucc] at hw
    simpa using hw
  have hmem : (∑ k : Fin 5, w k.castSucc • h k.castSucc) ∈
      Submodule.span (ZMod 3) (Set.range h) := by
    apply Submodule.sum_mem
    intro k _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k.castSucc, rfl⟩)
  have hw5 : w (Fin.last 5) = 0 := by
    by_contra hne
    have hu : w (Fin.last 5) • x = -(∑ k : Fin 5, w k.castSucc • h k.castSucc) := by
      rw [eq_neg_iff_add_eq_zero]
      rw [add_comm]
      exact hsum
    have hxmem : x ∈ Submodule.span (ZMod 3) (Set.range h) := by
      have hx' : x = (w (Fin.last 5))⁻¹ • (-(∑ k : Fin 5, w k.castSucc • h k.castSucc)) := by
        rw [← hu, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [hx']
      exact Submodule.smul_mem _ _ (Submodule.neg_mem _ hmem)
    exact hxnot hxmem
  have hsum5 : (∑ k : Fin 5, w k.castSucc • h k.castSucc) = 0 := by
    have h := hsum
    rw [hw5, zero_smul, add_zero] at h
    exact h
  have hwcast : ∀ k : Fin 5, w k.castSucc = 0 :=
    fun k => (Fintype.linearIndependent_iff.mp hli) (fun k => w k.castSucc) hsum5 k
  funext j
  fin_cases j
  · simpa using hwcast ⟨0, by omega⟩
  · simpa using hwcast ⟨1, by omega⟩
  · simpa using hwcast ⟨2, by omega⟩
  · simpa using hwcast ⟨3, by omega⟩
  · simpa using hwcast ⟨4, by omega⟩
  · simpa using hw5

private lemma l05nLMψ_inj {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Fin 6 → V} {x : V}
    (hxnot : x ∉ Submodule.span (ZMod 3) (Set.range h))
    (hli : LinearIndependent (ZMod 3) (fun k : Fin 5 => h k.castSucc)) :
    Function.Injective (l05nLMψ h x) := by
  intro a b hab
  have hzero : l05nLMψ h x (a - b) = 0 := by rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (l05nLMψ_ker hxnot hli (a - b) hzero)

private lemma l05nLM_α_ψ {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V} {x : V}
    (F : GGDepEFrame 3 h α x) (i : Fin 6) (w : Fin 6 → ZMod 3) :
    α i (l05nLMψ h x w) = ggDepAdot (ggDepELα i) w := by
  rw [l05nLMψ_apply, ggDepAdot, map_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [map_smul, smul_eq_mul]
  rw [mul_comm (ggDepELα i k) (w k)]
  congr 1
  by_cases hk : k.val < 5
  · rw [dif_pos hk, F.pair i k]
    have hkk : k = (⟨k.val, hk⟩ : Fin 5).castSucc := Fin.ext rfl
    rw [hkk, l05nLM_ELα_castSucc]
  · rw [dif_neg hk]
    have hk5 : k.val = 5 := by have := k.isLt; omega
    have hkk : k = Fin.last 5 := Fin.ext (by simpa [Fin.val_last] using hk5)
    rw [hkk, F.x_ker, l05nLM_ELα_last]

private lemma l05nLM_ELh_castSucc (k : Fin 5) :
    ggDepELh k.castSucc = Pi.single k.castSucc (1 : ZMod 3) := by
  funext j
  fin_cases k <;> fin_cases j <;> decide

private lemma l05nLM_ELx_single : ggDepELx = Pi.single (Fin.last 5) (1 : ZMod 3) := by
  funext j
  fin_cases j <;> decide

private lemma l05nLM_ELh_last :
    ggDepELh (Fin.last 5) =
      Pi.single (0 : Fin 6) (1 : ZMod 3) + (2 : ZMod 3) • Pi.single (2 : Fin 6) 1 +
        Pi.single (4 : Fin 6) 1 := by
  funext j
  fin_cases j <;> decide

private lemma l05nLM_ψ_ELh_last {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 6 → V) (x : V) (h5eq : h 5 = h 0 + (2 : ZMod 3) • h 2 + h 4) :
    l05nLMψ h x (ggDepELh (Fin.last 5)) = h (Fin.last 5) := by
  rw [l05nLM_ELh_last]
  simp only [map_add, map_smul, l05nLMψ_single]
  rw [dif_pos (show (0 : Fin 6).val < 5 by decide),
    dif_pos (show (2 : Fin 6).val < 5 by decide),
    dif_pos (show (4 : Fin 6).val < 5 by decide)]
  have hlast : (Fin.last 5 : Fin 6) = 5 := Fin.ext (by simp [Fin.val_last])
  rw [hlast, h5eq]

theorem ggDepELModel_iso {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Module.Finite (ZMod 3) V] {h : Fin 6 → V} {α : Fin 6 → Module.Dual (ZMod 3) V} {x : V}
    (F : GGDepEFrame 3 h α x) (hdim : Module.finrank (ZMod 3) V = 6) :
    ∃ θ : V ≃ₗ[ZMod 3] GGDepAE 3 6, (∀ i, θ (h i) = ggDepELh i) ∧
      (∀ i v, α i v = ggDepAdot (ggDepELα i) (θ v)) ∧ θ x = ggDepELx := by
  classical
  obtain ⟨hrel, hxnot, hfin⟩ := ggDepE_relation F
  have h5eq : h 5 = h 0 + (2 : ZMod 3) • h 2 + h 4 := by
    have h' : h 0 + (2 : ZMod 3) • h 2 + h 4 + (2 : ZMod 3) • h 5 = 0 := by
      simpa [Fin.sum_univ_six] using hrel
    have h5neg : (2 : ZMod 3) • h 5 = - h 5 := by
      have h2 : (2 : ZMod 3) = -1 := by decide
      rw [h2]
      exact neg_one_smul (ZMod 3) (h 5)
    rw [h5neg, add_neg_eq_zero] at h'
    exact h'.symm
  have hli : LinearIndependent (ZMod 3) (fun k : Fin 5 => h k.castSucc) := by
    have hspan_eq : Submodule.span (ZMod 3) (Set.range (fun k : Fin 5 => h k.castSucc)) =
        Submodule.span (ZMod 3) (Set.range h) := by
      apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro _ ⟨k, rfl⟩
        exact Submodule.subset_span ⟨k.castSucc, rfl⟩
      · apply Submodule.span_le.mpr
        rintro _ ⟨i, rfl⟩
        by_cases hi : i.val < 5
        · have hii : i = Fin.castSucc ⟨i.val, hi⟩ := Fin.ext rfl
          rw [hii]
          exact Submodule.subset_span ⟨⟨i.val, hi⟩, rfl⟩
        · have hi5 : i.val = 5 := by have := i.isLt; omega
          have hii : i = (5 : Fin 6) := Fin.ext hi5
          rw [hii, h5eq]
          exact Submodule.add_mem _ (Submodule.add_mem _
            (Submodule.subset_span ⟨0, rfl⟩)
            (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩)))
            (Submodule.subset_span ⟨4, rfl⟩)
    rw [linearIndependent_iff_card_eq_finrank_span]
    rw [Set.finrank, hspan_eq, Fintype.card_fin]
    exact hfin.symm
  have hinj : Function.Injective (l05nLMψ h x) := l05nLMψ_inj hxnot hli
  have hfin' : Module.finrank (ZMod 3) (Fin 6 → ZMod 3) = Module.finrank (ZMod 3) V := by
    rw [Module.finrank_fin_fun, hdim]
  let e : (Fin 6 → ZMod 3) ≃ₗ[ZMod 3] V :=
    (l05nLMψ h x).linearEquivOfInjective hinj hfin'
  have he : ∀ w, e w = l05nLMψ h x w := fun w =>
    LinearMap.linearEquivOfInjective_apply hinj hfin' w
  refine ⟨e.symm, ?_, ?_, ?_⟩
  · intro i
    rw [LinearEquiv.symm_apply_eq, he]
    by_cases hi : i.val < 5
    · have hii : i = (⟨i.val, hi⟩ : Fin 5).castSucc := Fin.ext rfl
      rw [hii, l05nLM_ELh_castSucc, l05nLMψ_single,
        dif_pos (show ((⟨i.val, hi⟩ : Fin 5).castSucc).val < 5 from hi)]
    · have hi5 : i.val = 5 := by have := i.isLt; omega
      have hii : i = Fin.last 5 := Fin.ext (by simpa [Fin.val_last] using hi5)
      rw [hii]
      exact (l05nLM_ψ_ELh_last h x h5eq).symm
  · intro i v
    have hα := l05nLM_α_ψ F i (e.symm v)
    rw [show l05nLMψ h x (e.symm v) = v from by
      rw [← he (e.symm v), LinearEquiv.apply_symm_apply]] at hα
    exact hα
  · rw [LinearEquiv.symm_apply_eq, he]
    rw [l05nLM_ELx_single, l05nLMψ_single]
    rfl

end CFSG.StandardType

end
