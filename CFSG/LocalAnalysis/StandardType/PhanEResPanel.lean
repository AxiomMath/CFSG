module

public import CFSG.LocalAnalysis.StandardType.PhanEStdBuilding
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabLevi
import CFSG.Monster.B.Geometry.Gallery

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.ClassicalInvolution.Phan.PhanE
  CFSG.AGLEmbeddingD2.ParabLevi
open scoped Pointwise

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "Φ" => RootSystem.ofCartan D.isFiniteType D.divisible

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)

private theorem hmbRP_inversionUnipotent_simple_le (hext : SteinbergExtras D n H)
    (i : Fin D.rank) :
    inversionUnipotent D ((cs).simple i) ≤ D.rootGroup (Pi.single i 1) := by
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨hγr, hpos, hneg⟩ := hγ
  by_cases hmem : γ ∈ (Φ).posExcept i
  · exfalso
    have h1 := (Φ).refl_mem_posExcept hmem
    rw [weylAction_simple] at hneg
    have h2 : 0 < ht ((reflection D.cartan i) γ) := h1.1.2
    omega
  · have hγ' : γ = Pi.single i 1 ∨ γ = 2 • Pi.single i 1 := by
      by_contra hc
      rw [not_or] at hc
      refine hmem ⟨⟨hγr, hpos⟩, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact hc
    rcases hγ' with rfl | rfl
    · exact le_rfl
    · exact hext.two_smul_le _ ((Φ).single_mem i) hγr

include hext in
theorem exists_mk_eq_of_mem_bruhatCell_simple (i : Fin D.rank) {c : K}
    (hc : c ∈ bruhatCell hct ((cs).simple i)) :
    ∃ x ∈ D.rootGroup (Pi.single i 1),
      (c : K ⧸ borel D H) = ((x * n i : K) : K ⧸ borel D H) := by
  have hcinv : c⁻¹ ∈ bruhatCell hct ((cs).simple i) := by
    have h1 : c⁻¹ ∈ (bruhatCell hct ((cs).simple i))⁻¹ := by
      rw [Set.mem_inv]
      simpa using hc
    rw [q2nPE_inv_cell hct hext ((cs).simple i), (cs).inv_simple] at h1
    exact h1
  obtain ⟨b, hb, u, hu, he⟩ := exists_eq_mul_nrep_mul hct hext hcinv
  rw [nrep_simple hct i] at he
  refine ⟨u⁻¹, inv_mem (hmbRP_inversionUnipotent_simple_le hext i hu), ?_⟩
  rw [QuotientGroup.eq]
  have heq : c⁻¹ * (u⁻¹ * n i) = b * (n i * n i) := by rw [he]; group
  rw [heq, ← pow_two]
  exact mul_mem hb (iSup_le_borel (sq_n_mem_iSup hct i))

include hext in
theorem exists_eq_of_stdδ_eq_simple {g : K} {z : K ⧸ borel D H} {i : Fin D.rank}
    (h : stdδ hct (g : K ⧸ borel D H) z = (cs).simple i) :
    ∃ x ∈ D.rootGroup (Pi.single i 1), z = ((g * x * n i : K) : K ⧸ borel D H) := by
  obtain ⟨h₀, rfl⟩ := QuotientGroup.mk_surjective z
  have hmem : g⁻¹ * h₀ ∈ bruhatCell hct ((cs).simple i) :=
    (stdδ_mk_eq_iff hct hext g h₀ ((cs).simple i)).mp h
  obtain ⟨x, hx, hxeq⟩ := exists_mk_eq_of_mem_bruhatCell_simple hct hext i hmem
  refine ⟨x, hx, ?_⟩
  rw [QuotientGroup.eq]
  have h1 := QuotientGroup.eq.mp hxeq
  convert h1 using 1
  group

include hext in
theorem stdδ_mk_mul_of_mem_rankOne (g : K) {i : Fin D.rank} {l : K}
    (hl : l ∈ rankOne D.rootGroup i) :
    stdδ hct (g : K ⧸ borel D H) ((g * l : K) : K ⧸ borel D H) = 1 ∨
      stdδ hct (g : K ⧸ borel D H) ((g * l : K) : K ⧸ borel D H) = (cs).simple i := by
  obtain ⟨P, hP, hres⟩ := std_residue_mk hct hext ({i} : Set (Fin D.rank))
  have hXpos : D.rootGroup (Pi.single i 1) ≤ P := by
    intro x hx
    show x ∈ (P : Set K)
    rw [hP]
    refine Set.mem_iUnion.2 ⟨1, Set.mem_iUnion.2 ⟨Subgroup.one_mem _, ?_⟩⟩
    rw [bruhatCell_one hct]
    exact rootGroup_le_borel ((Φ).single_mem i) (ht_single_pos i) hx
  have hnP : n i ∈ P := by
    show n i ∈ (P : Set K)
    rw [hP]
    refine Set.mem_iUnion.2 ⟨(cs).simple i, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
    · exact Subgroup.subset_closure (by simp)
    · rw [← nrep_simple hct i]
      exact nrep_mem_bruhatCell hct _
  have hXneg : D.rootGroup (-Pi.single i 1) ≤ P := by
    intro y hy
    have hmem : -Pi.single i 1 ∈ D.roots := (Φ).neg_mem _ ((Φ).single_mem i)
    have hconj : n i * y * (n i)⁻¹ ∈ D.rootGroup (Pi.single i 1) := by
      have h := hct.conj_mem i (-Pi.single i 1) hmem y hy
      rwa [map_neg, weylAction_simple_single D.isFiniteType i, neg_neg] at h
    have hyP : n i * y * (n i)⁻¹ ∈ P := hXpos hconj
    have e : y = (n i)⁻¹ * (n i * y * (n i)⁻¹) * n i := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hnP) hyP) hnP
  have hlP : l ∈ P := by
    have hl' : l ∈ D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1) := hl
    exact (sup_le hXpos hXneg) hl'
  have hglP : (g * l : K) ∈ g • (P : Set K) := by
    rw [Set.mem_smul_set]
    exact ⟨l, hlP, rfl⟩
  have hresid : ((g * l : K) : K ⧸ borel D H) ∈
      residue (cs) (stdδ hct) {i} (g : K ⧸ borel D H) := by
    rw [hres g]
    exact Set.mem_image_of_mem _ hglP
  exact (mem_panel_iff (stdBuilding hct hext) (i := i) (x := (g : K ⧸ borel D H))
    (y := ((g * l : K) : K ⧸ borel D H))).mp hresid

include hext in
private theorem hmbRP_mem_residue_of_mem_leviM {I : Set (Fin D.rank)} (g : K) {l : K}
    (hl : l ∈ leviM D I) :
    ((g * l : K) : K ⧸ borel D H) ∈ residue (cs) (stdδ hct) I (g : K ⧸ borel D H) := by
  have hle : leviM D I = ⨆ i : I, rankOne D.rootGroup (i : Fin D.rank) := by
    rw [leviM]
    exact (iSup_subtype'' I (fun i => rankOne D.rootGroup i)).symm
  rw [hle] at hl
  have hmain : ∀ g' : K, ((g' * l : K) : K ⧸ borel D H) ∈
      residue (cs) (stdδ hct) I (g' : K ⧸ borel D H) := by
    refine Subgroup.iSup_induction (S := fun i : I => rankOne D.rootGroup (i : Fin D.rank))
      (C := fun x : K => ∀ g' : K, ((g' * x : K) : K ⧸ borel D H) ∈
        residue (cs) (stdδ hct) I (g' : K ⧸ borel D H)) hl ?_ ?_ ?_
    · intro i x hx g'
      have hpan : ((g' * x : K) : K ⧸ borel D H) ∈
          residue (cs) (stdδ hct) ({(i : Fin D.rank)} : Set (Fin D.rank)) (g' : K ⧸ borel D H) :=
        (mem_panel_iff (stdBuilding hct hext) (i := (i : Fin D.rank))
          (x := (g' : K ⧸ borel D H)) (y := ((g' * x : K) : K ⧸ borel D H))).mpr
          (stdδ_mk_mul_of_mem_rankOne hct hext g' hx)
      exact residue_mono (Set.singleton_subset_iff.mpr i.2) (g' : K ⧸ borel D H) hpan
    · intro g'
      simpa using self_mem_residue I (g' : K ⧸ borel D H)
    · intro x y hx hy g'
      have h1 : ((g' * x : K) : K ⧸ borel D H) ∈
          residue (cs) (stdδ hct) I (g' : K ⧸ borel D H) := hx g'
      have h2 : (((g' * x) * y : K) : K ⧸ borel D H) ∈
          residue (cs) (stdδ hct) I ((g' * x : K) : K ⧸ borel D H) := hy (g' * x)
      rw [residue_eq_of_mem (stdBuilding hct hext) h1] at h2
      simpa only [mul_assoc] using h2
  exact hmain g

include hext in
theorem residue_eq_image_leviM (I : Set (Fin D.rank)) (g : K) :
    residue (cs) (stdδ hct) I (g : K ⧸ borel D H) =
      (fun l : K => ((g * l : K) : K ⧸ borel D H)) '' (leviM D I : Set K) := by
  apply le_antisymm
  · intro y hy
    induction hy with
    | refl => exact ⟨1, one_mem _, by simp⟩
    | tail _ hbc ih =>
      obtain ⟨i, hiI, hδi⟩ := hbc
      obtain ⟨l, hl, hl_eq⟩ := ih
      rw [← hl_eq] at hδi
      obtain ⟨x, hx, hxeq⟩ :=
        exists_eq_of_stdδ_eq_simple hct hext (i := i) (g := g * l) hδi
      refine ⟨l * x * n i, mul_mem (mul_mem hl ?_) ?_, ?_⟩
      · exact rankOne_le_leviM hiI (show x ∈ rankOne D.rootGroup i from Subgroup.mem_sup_left hx)
      · exact rankOne_le_leviM hiI (show n i ∈ rankOne D.rootGroup i from hct.n_mem i)
      · simpa only [mul_assoc] using hxeq.symm
  · rintro y ⟨l, hl, rfl⟩
    exact hmbRP_mem_residue_of_mem_leviM hct hext g hl

include hext in
theorem mk_mul_mem_residue_of_mem_leviM {I : Set (Fin D.rank)} (g : K) {l : K}
    (hl : l ∈ leviM D I) :
    ((g * l : K) : K ⧸ borel D H) ∈ residue (cs) (stdδ hct) I (g : K ⧸ borel D H) :=
  hmbRP_mem_residue_of_mem_leviM hct hext g hl

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
