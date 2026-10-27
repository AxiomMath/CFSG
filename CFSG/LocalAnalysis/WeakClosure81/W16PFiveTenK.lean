module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveTenKTriv
public import CFSG.LocalAnalysis.WeakClosure81.SevenKFactsBar
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveTenKHom

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

private theorem shape166_conjSubgroup {X : Type} [Group X] {Y : Subgroup X} {n : ℕ}
    (hX : Shape166 X Y n) (g : X) : Shape166 X (conjSubgroup Y g) n := by
  let f : X →* X := (MulAut.conj g⁻¹).toMonoidHom
  have hfsurj : Function.Surjective f := (MulAut.conj g⁻¹).surjective
  obtain ⟨hcard, hcase⟩ := hX
  refine ⟨?_, ?_⟩
  · change Nat.card (Y.map f) = 2 ^ n
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hcard]
  · rcases hcase with ⟨hn1, hD⟩ | ⟨hn1, hsup, p, hp, hO⟩
    · exact Or.inl ⟨hn1, hD⟩
    · refine Or.inr ⟨hn1, ?_, p, hp, hO⟩
      have hOm : (fusionOddCore X).map f = fusionOddCore X := by
        simpa [f] using Subgroup.normal_iff_map_conj_eq.mp (fusionOddCore_normal X) g⁻¹
      have hmap : conjSubgroup Y g ⊔ fusionOddCore X = (Y ⊔ fusionOddCore X).map f := by
        calc conjSubgroup Y g ⊔ fusionOddCore X
            = Y.map f ⊔ (fusionOddCore X).map f := by
                rw [show conjSubgroup Y g = Y.map f from rfl, hOm]
          _ = (Y ⊔ fusionOddCore X).map f := (Subgroup.map_sup Y (fusionOddCore X) f).symm
      rw [hmap, hsup, Subgroup.map_top_of_surjective f hfsurj]

theorem IsMinFam16.exists_mem_not_le_conj
    (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (hQ : pCoreOf 2 (conjClosure V H) ≤ centralizer (iSub16 V H : Set G))
    {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (conjClosure V H) (pCoreOf 2 (conjClosure V H)) φ) {n : ℕ}
    (hX : Shape166 X (SevenK.barSub (conjClosure V H) φ V) n) {x : G}
    (hxS : conjSubgroup V x ≤ S) (hxk : ¬ conjSubgroup V x ≤ kerMOf M H)
    (h9 : ∀ a ∈ conjSubgroup V x, ∃ v ∈ V, ∀ k ∈ conjClosure V H,
      (a * v⁻¹) * k * (a * v⁻¹)⁻¹ * k⁻¹ ∈ pCoreOf 2 (conjClosure V H)) :
    ∃ k ∈ conjClosure V H, ¬ conjSubgroup V k ≤ conjSubgroup M x ∧
      ¬ conjSubgroup V x ≤ conjSubgroup M k := by
  classical
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  let K : Subgroup G := conjClosure V H
  let A : Subgroup G := conjSubgroup V x
  let Vb : Subgroup X := SevenK.barSub (conjClosure V H) φ V
  obtain ⟨w, hwVb, hw⟩ := IsMinFam16.exists_hom_of_comm_mem h1 hS h hH hV hφ hX hxS h9
  obtain ⟨a₀, ha₀⟩ := IsMinFam16.exists_hom_ne_one h1 h5 hS h hH hV hQ hφ hxS hxk hw
  have hY : IsElemAbelian 2 Vb := isElemAbelian_barSub h.hyp.h6.elemAbelian φ
  have hgen : normalClosure (Vb : Set X) = ⊤ :=
    IsMinFam16.normalClosure_barSub_eq_top h1 hS h hH hV hφ
  obtain ⟨y, hy⟩ := Shape166.exists_conj_ne hY hgen hX
  let Wbar : Subgroup X := w.range
  have hWbar_le : Wbar ≤ Vb := by
    intro c hc
    rcases hc with ⟨a, rfl⟩
    exact hwVb a
  have hWbar_ne : Wbar ≠ ⊥ := by
    intro hbot
    have hc : w a₀ ∈ Wbar := ⟨a₀, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hc
    exact ha₀ hc
  have hVb_ne : Vb ≠ ⊥ := fun hbot => hWbar_ne (le_bot_iff.1 (hbot ▸ hWbar_le))
  obtain ⟨kK, hkK⟩ := hφ.surjective y
  have hKK : conjClosure V K = K :=
    IsMinFam16.conjClosure_conjClosure_eq h1 hS h hH hV
  have hconj_le_K : conjSubgroup V (kK : G) ≤ K := by
    intro z hz
    rw [conjSubgroup, Subgroup.mem_map] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    have hmem : (kK : G)⁻¹ * v * ((kK : G)⁻¹)⁻¹ ∈ conjClosure V K :=
      CFSG.Quasithin.mem_conjClosure (Z := V) (H := K) (K.inv_mem kK.2) hv
    rw [← hKK]
    exact hmem
  refine ⟨(kK : G), kK.2, ?_, ?_⟩
  · intro hcase1
    have hMn : conjSubgroup M x = Subgroup.normalizer (A : Set G) := by
      rw [← h.hyp.h6.normalizer_eq]
      exact conjSubgroup_normalizer V x
    have hcase1' : conjSubgroup V (kK : G) ≤ Subgroup.normalizer (A : Set G) := by
      rw [← hMn]
      exact hcase1
    have hnorm : conjSubgroup Vb y ≤ Subgroup.normalizer (Wbar : Set X) := by
      rw [← hkK, ← barSub_conjSubgroup φ V kK]
      refine Subgroup.le_normalizer_iff.mpr fun b hb c hc => ?_
      rw [SevenK.mem_barSub] at hb
      obtain ⟨u, hu_mem, rfl⟩ := hb
      rcases hc with ⟨a, rfl⟩
      have hu_mem' : (u : G) ∈ Subgroup.normalizer (A : Set G) := hcase1' hu_mem
      have hamem : (u : G) * (a : G) * (u : G)⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp hu_mem' (a : G)).mp a.2
      let a' : ↥A := ⟨(u : G) * (a : G) * (u : G)⁻¹, hamem⟩
      refine ⟨a', ?_⟩
      rw [IsMinFam16.hom_conj_eq h1 hS h hH hV hφ hX hxS hwVb hw hu_mem'
        (a := a) (a' := a') rfl]
    have hbot := Shape166.conj_inf_normalizer_eq_bot hY hgen hX hWbar_le hWbar_ne hy
    have hZbot : conjSubgroup Vb y = ⊥ := by
      rw [← inf_eq_left.mpr hnorm]
      exact hbot
    have hVbbot : Vb = ⊥ := by
      have h2 := congrArg (fun T : Subgroup X => conjSubgroup T y⁻¹) hZbot
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h2
      have h3 : conjSubgroup (⊥ : Subgroup X) y⁻¹ = ⊥ := by
        simp only [conjSubgroup, Subgroup.map_bot]
      rwa [h3] at h2
    exact hVb_ne hVbbot
  · intro hcase2
    have hMnk : conjSubgroup M (kK : G) =
        Subgroup.normalizer (conjSubgroup V (kK : G) : Set G) := by
      rw [← h.hyp.h6.normalizer_eq]
      exact conjSubgroup_normalizer V (kK : G)
    have hcase2' : A ≤ Subgroup.normalizer (conjSubgroup V (kK : G) : Set G) := by
      rw [← hMnk]
      exact hcase2
    have hZ_ne : conjSubgroup Vb y ≠ ⊥ := by
      intro hbot
      apply hVb_ne
      have h2 := congrArg (fun T : Subgroup X => conjSubgroup T y⁻¹) hbot
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at h2
      have h3 : conjSubgroup (⊥ : Subgroup X) y⁻¹ = ⊥ := by
        simp only [conjSubgroup, Subgroup.map_bot]
      rwa [h3] at h2
    have hYZ : IsElemAbelian 2 (conjSubgroup Vb y) := by
      have h := hY.map (MulAut.conj y⁻¹).toMonoidHom
      rwa [show Vb.map (MulAut.conj y⁻¹).toMonoidHom = conjSubgroup Vb y from rfl] at h
    have hgenZ : normalClosure (conjSubgroup Vb y : Set X) = ⊤ := by
      have hmap := Subgroup.map_normalClosure (Vb : Set X) (MulAut.conj y⁻¹).toMonoidHom
        (MulAut.conj y⁻¹).surjective
      have hcoe : ((conjSubgroup Vb y : Subgroup X) : Set X) =
          (MulAut.conj y⁻¹).toMonoidHom '' (Vb : Set X) :=
        Subgroup.coe_map (MulAut.conj y⁻¹).toMonoidHom Vb
      rw [hcoe, ← hmap, hgen, Subgroup.map_top_of_surjective _ (MulAut.conj y⁻¹).surjective]
    have hXZ : Shape166 X (conjSubgroup Vb y) n := shape166_conjSubgroup hX y
    have hWleN : Wbar ≤ Subgroup.normalizer (conjSubgroup Vb y : Set X) := by
      rw [← hkK, ← barSub_conjSubgroup φ V kK]
      refine Subgroup.le_normalizer_iff.mpr fun c hc d hd => ?_
      rcases hc with ⟨a, rfl⟩
      rw [SevenK.mem_barSub] at hd
      obtain ⟨u, hu_mem, rfl⟩ := hd
      have haN : (a : G) ∈ Subgroup.normalizer (conjSubgroup V (kK : G) : Set G) := hcase2' a.2
      have hmem : (a : G) * (u : G) * (a : G)⁻¹ ∈ conjSubgroup V (kK : G) :=
        (Subgroup.mem_normalizer_iff.mp haN (u : G)).mp hu_mem
      let u' : ↥K := ⟨(a : G) * (u : G) * (a : G)⁻¹, hconj_le_K hmem⟩
      rw [← hw a u u' rfl]
      exact SevenK.mem_barSub.mpr ⟨u', hmem, rfl⟩
    have hTI := Shape166.conj_inf_normalizer_eq_bot hYZ hgenZ hXZ (le_refl _) hZ_ne
      (x := y⁻¹) (by
        rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
        exact fun hEq => hy hEq.symm)
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at hTI
    have hle : Wbar ≤ Vb ⊓ Subgroup.normalizer (conjSubgroup Vb y : Set X) :=
      le_inf hWbar_le hWleN
    have hle' : Wbar ≤ (⊥ : Subgroup X) := by
      rw [← hTI]
      exact hle
    exact hWbar_ne (le_bot_iff.1 hle')

end CFSG.LocalAnalysis.WeakClosure81

end
