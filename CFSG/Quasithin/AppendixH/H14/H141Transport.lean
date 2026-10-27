module

public import CFSG.Quasithin.AppendixH.H14.H142Group
public import CFSG.Quasithin.AppendixH.H14.H142Conj

public section

open scoped Pointwise

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI.ChH CFSG.Open CFSG.Quasithin

theorem map_conj_M24g {c : S24} (hc : c ∈ M24g) :
    M24g.map (MulAut.conj c).toMonoidHom = M24g := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact M24g.mul_mem (M24g.mul_mem hc hy) (M24g.inv_mem hc)
  · intro x hx
    refine ⟨c⁻¹ * x * c, M24g.mul_mem (M24g.mul_mem (M24g.inv_mem hc) hx) hc, ?_⟩
    show c * (c⁻¹ * x * c) * c⁻¹ = x
    group

theorem MY_smul {α : Type*} [MulAction S24 α] {c : S24} (hc : c ∈ M24g) (Y : α) :
    MY M24g (c • Y) = (MY M24g Y).map (MulAut.conj c).toMonoidHom := by
  unfold MY
  rw [map_conj_inf_stabilizer c M24g Y, map_conj_M24g hc]

theorem KY_smul {α : Type*} [MulAction S24 α] {c : S24} (hc : c ∈ M24g) (Y : α) :
    KY M24g (c • Y) = (KY M24g Y).map (MulAut.conj c).toMonoidHom := by
  unfold KY
  rw [MY_smul hc Y, pCoreOf_map_conj 2 c (MY M24g Y)]

theorem perfectCore_map_conj (c : S24) (H : Subgroup S24) :
    perfectCore (H.map (MulAut.conj c).toMonoidHom) =
      (perfectCore H).map (MulAut.conj c).toMonoidHom := by
  exact (map_perfectCore (MulAut.conj c).toMonoidHom H).symm

theorem map_conj_conjSubg (c g : S24) (X : Subgroup S24) :
    conjSubg ((MulAut.conj c).toMonoidHom g) (X.map (MulAut.conj c).toMonoidHom) =
      (conjSubg g X).map (MulAut.conj c).toMonoidHom := by
  have hcomp : (MulAut.conj ((MulAut.conj c).toMonoidHom g)).toMonoidHom.comp
        (MulAut.conj c).toMonoidHom =
      (MulAut.conj c).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  simp only [conjSubg, Subgroup.map_map]
  rw [hcomp]

theorem conjIso_of_map_conj (c : S24) {G K : Subgroup S24} {A : Type*} [CommGroup A]
    {Γ : Set (MulAut A)}
    (φ' : ↥(K.map (MulAut.conj c).toMonoidHom) ≃* A)
    (π' : ↥(G.map (MulAut.conj c).toMonoidHom) →* MulAut A)
    (h : ConjIso (G.map (MulAut.conj c).toMonoidHom) (K.map (MulAut.conj c).toMonoidHom) A Γ φ' π')
    (hf : Function.Injective (MulAut.conj c).toMonoidHom) :
    ConjIso G K A Γ
      ((Subgroup.equivMapOfInjective K (MulAut.conj c).toMonoidHom hf).trans φ')
      (π'.comp (Subgroup.equivMapOfInjective G (MulAut.conj c).toMonoidHom hf).toMonoidHom) := by
  unfold ConjIso at h ⊢
  obtain ⟨hKG', h1', h2', hker', hact'⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.map_le_map_iff_of_injective hf).mp hKG'
  · intro g
    exact h1' (Subgroup.equivMapOfInjective G (MulAut.conj c).toMonoidHom hf g)
  · intro γ hγ
    obtain ⟨g', hg'⟩ := h2' γ hγ
    refine ⟨(Subgroup.equivMapOfInjective G (MulAut.conj c).toMonoidHom hf).symm g', ?_⟩
    change π' (Subgroup.equivMapOfInjective G (MulAut.conj c).toMonoidHom hf
      ((Subgroup.equivMapOfInjective G (MulAut.conj c).toMonoidHom hf).symm g')) = γ
    rw [MulEquiv.apply_symm_apply]
    exact hg'
  · intro g
    have hstep := hker' (Subgroup.equivMapOfInjective G (MulAut.conj c).toMonoidHom hf g)
    change (π' (Subgroup.equivMapOfInjective G (MulAut.conj c).toMonoidHom hf g) = 1) ↔
      (g : S24) ∈ K
    rw [hstep, Subgroup.coe_equivMapOfInjective_apply]
    exact Subgroup.mem_map_iff_mem hf
  · intro g k k' hk
    have hkk : ((Subgroup.equivMapOfInjective K (MulAut.conj c).toMonoidHom hf k' :
          ↥(K.map (MulAut.conj c).toMonoidHom)) : S24) =
        ((Subgroup.equivMapOfInjective G (MulAut.conj c).toMonoidHom hf g :
            ↥(G.map (MulAut.conj c).toMonoidHom)) : S24) *
          ((Subgroup.equivMapOfInjective K (MulAut.conj c).toMonoidHom hf k :
            ↥(K.map (MulAut.conj c).toMonoidHom)) : S24) *
          ((Subgroup.equivMapOfInjective G (MulAut.conj c).toMonoidHom hf g :
            ↥(G.map (MulAut.conj c).toMonoidHom)) : S24)⁻¹ := by
      simp only [Subgroup.coe_equivMapOfInjective_apply]
      rw [hk]
      simp only [map_mul, map_inv]
    have hact := hact' (Subgroup.equivMapOfInjective G (MulAut.conj c).toMonoidHom hf g)
      (Subgroup.equivMapOfInjective K (MulAut.conj c).toMonoidHom hf k)
      (Subgroup.equivMapOfInjective K (MulAut.conj c).toMonoidHom hf k') hkk
    exact hact

@[expose] def Clause26 (MS KS KO : Subgroup S24) : Prop :=
  ∃ (K : Type) (_ : Field K), Nat.card K = 4 ∧
    ∃ (Ω : Set (Submodule K (Fin 3 → K))) (φ : ↥KS ≃* Multiplicative (Fin 3 → K))
      (π : ↥MS →* MulAut (Multiplicative (Fin 3 → K))),
      IsHyperoval K Ω ∧ ConjIso MS KS (Multiplicative (Fin 3 → K)) (hatS6set K Ω) φ π ∧
        (∀ g : ↥MS, (g : S24) ∈ perfectCore MS → IsKLinearAut (π g)) ∧
        IsE2k 2 (KO ⊓ KS) ∧
        (∃ w : Fin 3 → K, w ≠ 0 ∧ ∀ k : ↥KS,
          (k : S24) ∈ KO ⊓ KS ↔ ∃ c : K, Multiplicative.toAdd (φ k) = c • w) ∧
        Set.ncard {C : Subgroup S24 | ∃ g ∈ MS, C = conjSubg g (KO ⊓ KS)} = 15

theorem clause26_of_map_conj (c : S24) {MS KS KO : Subgroup S24}
    (h : Clause26 (MS.map (MulAut.conj c).toMonoidHom) (KS.map (MulAut.conj c).toMonoidHom)
      (KO.map (MulAut.conj c).toMonoidHom)) : Clause26 MS KS KO := by
  have hf : Function.Injective (MulAut.conj c).toMonoidHom := by
    simpa only [MulEquiv.coe_toMonoidHom] using (MulAut.conj c).injective
  unfold Clause26 at h
  obtain ⟨K, hKfield, hKcard, Ω, φ', π', hHyp, hConj, hLin, hE2k, hLine, hCount⟩ := h
  letI : Field K := hKfield
  let eK := Subgroup.equivMapOfInjective KS (MulAut.conj c).toMonoidHom hf
  let eM := Subgroup.equivMapOfInjective MS (MulAut.conj c).toMonoidHom hf
  let φ : ↥KS ≃* Multiplicative (Fin 3 → K) := eK.trans φ'
  let π : ↥MS →* MulAut (Multiplicative (Fin 3 → K)) := π'.comp eM.toMonoidHom
  refine ⟨K, hKfield, hKcard, Ω, φ, π, hHyp, ?_, ?_, ?_, ?_, ?_⟩
  · exact conjIso_of_map_conj c φ' π' hConj hf
  · intro g hg
    have hg' : (eM g : S24) ∈ perfectCore (MS.map (MulAut.conj c).toMonoidHom) := by
      rw [perfectCore_map_conj c MS, Subgroup.mem_map]
      exact ⟨(g : S24), hg,
        (Subgroup.coe_equivMapOfInjective_apply (H := MS) (f := (MulAut.conj c).toMonoidHom) hf g).symm⟩
    exact hLin (eM g) hg'
  · refine ⟨?_, ?_⟩
    · apply isElemAbelian_of_map_conj 2 c
      rw [Subgroup.map_inf KO KS (MulAut.conj c).toMonoidHom hf]
      exact hE2k.1
    · have hcard := hE2k.2
      rw [← Subgroup.map_inf KO KS (MulAut.conj c).toMonoidHom hf, card_map_conj] at hcard
      exact hcard
  · obtain ⟨w, hwne, hw⟩ := hLine
    refine ⟨w, hwne, ?_⟩
    intro k
    have hk : (k : S24) ∈ KO ⊓ KS ↔
        (eK k : S24) ∈ KO.map (MulAut.conj c).toMonoidHom ⊓
          KS.map (MulAut.conj c).toMonoidHom := by
      rw [← Subgroup.map_inf KO KS (MulAut.conj c).toMonoidHom hf,
        Subgroup.coe_equivMapOfInjective_apply (H := KS) (f := (MulAut.conj c).toMonoidHom) hf k]
      exact (Subgroup.mem_map_iff_mem hf).symm
    rw [hk]
    have hw' := hw (eK k)
    exact hw'
  · rw [← hCount]
    have hmap : (fun C : Subgroup S24 => C.map (MulAut.conj c).toMonoidHom) ''
          {C : Subgroup S24 | ∃ g ∈ MS, C = conjSubg g (KO ⊓ KS)} =
          {C : Subgroup S24 | ∃ g ∈ MS.map (MulAut.conj c).toMonoidHom,
            C = conjSubg g (KO.map (MulAut.conj c).toMonoidHom ⊓
              KS.map (MulAut.conj c).toMonoidHom)} := by
      ext C
      constructor
      · rintro ⟨D, ⟨g, hg, rfl⟩, rfl⟩
        refine ⟨(MulAut.conj c).toMonoidHom g, ⟨g, hg, rfl⟩, ?_⟩
        dsimp only
        rw [← map_conj_conjSubg c g (KO ⊓ KS),
          Subgroup.map_inf KO KS (MulAut.conj c).toMonoidHom hf]
      · rintro ⟨g', hg', rfl⟩
        obtain ⟨g, hg, hgg'⟩ := Subgroup.mem_map.mp hg'
        refine ⟨conjSubg g (KO ⊓ KS), ⟨g, hg, rfl⟩, ?_⟩
        dsimp only
        rw [← hgg', ← map_conj_conjSubg c g (KO ⊓ KS),
          Subgroup.map_inf KO KS (MulAut.conj c).toMonoidHom hf]
    rw [← hmap]
    exact (Set.ncard_image_of_injective _
      (Subgroup.map_injective hf)).symm

end CFSG.Quasithin.AppendixH.H14
