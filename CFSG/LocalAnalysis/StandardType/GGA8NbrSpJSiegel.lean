module

public import CFSG.LocalAnalysis.StandardType.GGA8NbrSpJClass
public import CFSG.LocalAnalysis.StandardType.GGA8NbrOrder73
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionLinear

public section

namespace CFSG.StandardType.A8Coord

open CFSG.Assembly CFSG.Open CFSG.StandardType
open CFSG.StandardType.CoordSp CFSG.LieType.Universal.Symplectic.SpExtras
open CFSG.ClassicalInvolution.Models.SymplecticPairs

private theorem a8jg_permMatrix_apply {F : Type} [Field F] {n : ℕ} (σ : Equiv.Perm (Fin n))
    (i j : Fin n) :
    Equiv.Perm.permMatrix F σ i j = if σ i = j then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

private theorem a8jg_signedPerm_false_inv_inl (π : Equiv.Perm (Fin 3)) (i : Fin 3) :
    (CoordSp.signedPerm (fun _ => false) π)⁻¹ (Sum.inl i) = Sum.inl (π⁻¹ i) := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
  simp [CoordSp.signedPerm_inl]

private theorem a8jg_signedPerm_false_inv_inr (π : Equiv.Perm (Fin 3)) (i : Fin 3) :
    (CoordSp.signedPerm (fun _ => false) π)⁻¹ (Sum.inr i) = Sum.inr (π⁻¹ i) := by
  rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
  simp [CoordSp.signedPerm_inr]

private theorem a8jg_mat_spPerm_block (π : Equiv.Perm (Fin 3)) :
    mat 3 (GaloisField 2 3) (CoordSp.spPerm (F := GaloisField 2 3) (fun _ => false) π) =
      Matrix.fromBlocks (Equiv.Perm.permMatrix (GaloisField 2 3) π⁻¹) 0 0
        (Equiv.Perm.permMatrix (GaloisField 2 3) π⁻¹) := by
  rw [mat_apply]
  change (((TauCeti.permutationGL (CoordSp.signedPerm (fun _ => false) π) :
    GL (Fin 3 ⊕ Fin 3) (GaloisField 2 3)) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3)
    (GaloisField 2 3))) = _
  rw [TauCeti.permutationGL_coe]
  ext a b
  rcases a with i | i <;> rcases b with j | j <;>
    simp [a8jg_signedPerm_false_inv_inl, a8jg_signedPerm_false_inv_inr, Matrix.fromBlocks,
      a8jg_permMatrix_apply, Pi.single_apply, eq_comm]

private theorem a8jg_enum_univ :
    (CoordSp.enum (Finset.univ : Finset (Fin 3)) : Fin 3 → Fin 3) = id := by
  funext k
  have h := Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin 3))) rfl
    (fun x => Finset.mem_univ x) strictMono_id
  exact congrFun h.symm k

private theorem a8jg_wtPres_spPerm (π : Equiv.Perm (Fin 3)) :
    CoordSp.WtPres (fun _ : Fin 3 => (1 : ZMod 7))
      (mat 3 (GaloisField 2 3)
        (CoordSp.spPerm (F := GaloisField 2 3) (fun _ => false) π)) := by
  rw [a8jg_mat_spPerm_block]
  intro a b hab
  rcases a with i | i <;> rcases b with j | j <;>
    simp [CoordSp.spWt, Matrix.fromBlocks] at hab ⊢

private theorem a8jg_eBlock_spPerm (π : Equiv.Perm (Fin 3)) :
    CoordSp.eBlock (Finset.univ : Finset (Fin 3))
      (mat 3 (GaloisField 2 3)
        (CoordSp.spPerm (F := GaloisField 2 3) (fun _ => false) π)) =
      Equiv.Perm.permMatrix (GaloisField 2 3) π⁻¹ := by
  rw [a8jg_mat_spPerm_block]
  ext k l
  rw [CoordSp.eBlock_apply, a8jg_enum_univ]
  change (Equiv.Perm.permMatrix (GaloisField 2 3) π⁻¹ k l =
    Equiv.Perm.permMatrix (GaloisField 2 3) π⁻¹ k l)
  rfl

private theorem a8jg_perm_mem_classHom_univ (π : Equiv.Perm (Fin 3)) :
    CoordSp.spPerm (F := GaloisField 2 3) (fun _ => false) π ∈
      (CoordSp.classHom (F := GaloisField 2 3) (Finset.univ : Finset (Fin 3))).range := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hsp : CoordSp.spClass (fun _ : Fin 3 => (1 : ZMod 7)) (1 : ZMod 7) =
      (Finset.univ : Finset (Fin 3)) := by
    ext i
    simp [CoordSp.spClass]
  rw [← hsp]
  refine CoordSp.mem_range_classHom (F := GaloisField 2 3) (n := 3) (p := 7)
    (β := fun _ : Fin 3 => (1 : ZMod 7)) (c := 1) (by norm_num) (by norm_num) ?_ ?_ ?_
  · exact a8jg_wtPres_spPerm π
  · rw [mem_suppGroup]
    intro r t hrt
    exact absurd ⟨by simp [hsp, planeSet], by simp [hsp, planeSet]⟩ hrt
  · rw [hsp, a8jg_eBlock_spPerm]
    exact CFSG.StandardType.det_permMatrix_charTwo π⁻¹

private theorem a8jg_order73_SL3 :
    ∃ s : Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 3), orderOf s = 73 := by
  haveI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  haveI : Fact (Nat.Prime 73) := ⟨by norm_num⟩
  have h73 : 73 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 3)) := by
    rw [Matrix.card_SL_field (𝔽 := GaloisField 2 3) 3]
    have hq : Fintype.card (GaloisField 2 3) = 8 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by norm_num)]
      norm_num
    rw [hq]
    norm_num [Fin.prod_univ_three]
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card'
    (G := Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 3)) 73 h73
  exact ⟨s, hs⟩

private theorem a8jg_exists_order73_SL {m : ℕ} (hm : m = 3) :
    ∃ s : Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 3), orderOf s = 73 := by
  obtain rfl : m = 3 := hm
  exact a8jg_order73_SL3

theorem ggA8Nbr_spSiegel {G : Type} [Group G] [Finite G]
    {ψ : StatedSp 3 (GaloisField 2 3) →* G} (hψ : Function.Injective ψ)
    {A₀ : StatedSp 3 (GaloisField 2 3)} {ζ : (GaloisField 2 3)ˣ} {hζ : ζ ^ 7 = 1}
    {β : Fin 3 → ZMod 7} {c : ZMod 7} (hall : CoordSp.spClass β c = Finset.univ) {J : Subgroup G}
    (hJ : J = ((CoordSp.classHom (F := GaloisField 2 3) (CoordSp.spClass β c)).range).map
      (CoordSp.frameConj ψ A₀)) :
    (∃ w ∈ J, orderOf w = 73) ∧
      ∀ π : Equiv.Perm (Fin 3),
        ∃ w ∈ J ⊓ Subgroup.normalizer ((CoordSp.frameHom ψ A₀ hζ).range : Set G),
          ∀ t : Fin 3 → ZMod 7,
            w⁻¹ * CoordSp.frameHom ψ A₀ hζ (Multiplicative.ofAdd t) * w =
              CoordSp.frameHom ψ A₀ hζ (Multiplicative.ofAdd fun i => t (π i)) := by
  have hcard : (CoordSp.spClass β c).card = 3 := by
    rw [hall]
    simp
  obtain ⟨S, hS⟩ := a8jg_exists_order73_SL hcard
  have hinj : Function.Injective
      ((CoordSp.frameConj ψ A₀).comp
        (CoordSp.classHom (F := GaloisField 2 3) (CoordSp.spClass β c))) :=
    (CoordSp.frameConj_injective hψ A₀).comp (CoordSp.classHom_injective _)
  refine ⟨⟨CoordSp.frameConj ψ A₀ (CoordSp.classHom (CoordSp.spClass β c) S), ?_, ?_⟩, ?_⟩
  · rw [hJ]
    exact Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.mpr ⟨S, rfl⟩)
  · exact (orderOf_injective _ hinj S).trans hS
  · intro π
    let w : G := CoordSp.frameConj ψ A₀
      (CoordSp.spPerm (F := GaloisField 2 3) (fun _ => false) π)
    have hmem : CoordSp.spPerm (F := GaloisField 2 3) (fun _ => false) π ∈
        (CoordSp.classHom (F := GaloisField 2 3) (CoordSp.spClass β c)).range := by
      rw [hall]
      exact a8jg_perm_mem_classHom_univ π
    have hwJ : w ∈ J := by
      rw [hJ]
      exact Subgroup.mem_map_of_mem _ hmem
    have haction : ∀ t : Fin 3 → ZMod 7,
        w⁻¹ * CoordSp.frameHom ψ A₀ hζ (Multiplicative.ofAdd t) * w =
          CoordSp.frameHom ψ A₀ hζ (Multiplicative.ofAdd fun i => t (π i)) := by
      intro t
      rw [CoordSp.frameHom_eq_frameConj]
      change (CoordSp.frameConj ψ A₀
            (CoordSp.spPerm (F := GaloisField 2 3) (fun _ => false) π))⁻¹ *
          CoordSp.frameConj ψ A₀ (CoordSp.spDiag (fun i => ζ ^ (t i).val)) *
          CoordSp.frameConj ψ A₀
            (CoordSp.spPerm (F := GaloisField 2 3) (fun _ => false) π) = _
      rw [← map_inv, ← map_mul, ← map_mul, CoordSp.spPerm_conj_spDiag]
      rw [CoordSp.frameHom_eq_frameConj]
      congr 1
    have hwN : w ∈ Subgroup.normalizer ((CoordSp.frameHom ψ A₀ hζ).range : Set G) := by
      refine CoordSL.mem_normalizer_range_of_conj (ι := CoordSp.frameHom ψ A₀ hζ) π
        (fun _ => 1) ?_
      intro t
      rw [haction t]
      congr 1
      funext i
      simp
    exact ⟨w, Subgroup.mem_inf.mpr ⟨hwJ, hwN⟩, haction⟩

end CFSG.StandardType.A8Coord

end
