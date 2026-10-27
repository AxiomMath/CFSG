module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UMat
public import CFSG.RepresentationTheory.UniqueVectorOrbitTwisting
public import CFSG.RankThree.PartOne.S12.InputsSec15

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup Matrix
open CFSG.RepresentationTheory (IsIrreducibleMatrixRep)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

theorem u81_sub_diagonal_zero {R : Type*} [CommRing R] (v : Fin 3 → R) :
    v - diagonal ![-1, 1, 1] *ᵥ v = (2 : R) • Pi.single 0 (v 0) := by
  ext j
  rw [Pi.sub_apply, mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  rcases eq_or_ne j 0 with rfl | hj
  · rw [Pi.single_eq_same, show ![(-1 : R), 1, 1] 0 = -1 from rfl]
    ring
  · rw [Pi.single_eq_of_ne hj, mul_zero]
    fin_cases j <;> simp at hj ⊢

theorem u81_sub_diagonal_one {R : Type*} [CommRing R] (v : Fin 3 → R) :
    v - diagonal ![1, -1, 1] *ᵥ v = (2 : R) • Pi.single 1 (v 1) := by
  ext j
  rw [Pi.sub_apply, mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  rcases eq_or_ne j 1 with rfl | hj
  · rw [Pi.single_eq_same, show ![(1 : R), -1, 1] 1 = -1 from rfl]
    ring
  · rw [Pi.single_eq_of_ne hj, mul_zero]
    fin_cases j <;> simp at hj ⊢

theorem u81_eq_sum_single {R : Type*} [AddCommMonoid R] (v : Fin 3 → R) :
    v = Pi.single 0 (v 0) + Pi.single 1 (v 1) + Pi.single 2 (v 2) :=
  (Finset.univ_sum_single v).symm.trans (Fin.sum_univ_three _)

namespace U81Frame

variable {G : Type*} [Group G] {r : ℕ} {B : Subgroup G} {b : Fin 3 → G} [NeZero r]

theorem isIrreducible [Finite G] [Fact r.Prime] (hF : U81Frame r B b) (hr2 : r ≠ 2)
    {t₁ t₂ : normalizer (B : Set G)}
    (ht₁ : (hF.rho t₁ : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal ![-1, 1, 1])
    (ht₂ : (hF.rho t₂ : Matrix (Fin 3) (Fin 3) (ZMod r)) = diagonal ![1, -1, 1])
    (hU : ∀ I : Finset (Fin 3), I.Nonempty → I ≠ Finset.univ →
      ¬ normalizer (B : Set G) ≤ normalizer ((closure (b '' (I : Set (Fin 3))) : Subgroup G) :
        Set G)) :
    IsIrreducibleMatrixRep hF.rho.range.subtype := by
  classical
  intro S hS
  have hSm : ∀ m : normalizer (B : Set G), ∀ v ∈ S,
      (hF.rho m : Matrix (Fin 3) (Fin 3) (ZMod r)) *ᵥ v ∈ S :=
    fun m v hv => hS ⟨hF.rho m, m, rfl⟩ v hv
  have h2 : (2 : ZMod r) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hr2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) Nat.prime_two).1 h')
  have hcomp : ∀ v ∈ S, ∀ i, Pi.single i (v i) ∈ S := by
    intro v hv
    have e0 : (2 : ZMod r) • Pi.single 0 (v 0) =
        v - (hF.rho t₁ : Matrix (Fin 3) (Fin 3) (ZMod r)) *ᵥ v := by
      rw [ht₁]
      exact (u81_sub_diagonal_zero v).symm
    have e1 : (2 : ZMod r) • Pi.single 1 (v 1) =
        v - (hF.rho t₂ : Matrix (Fin 3) (Fin 3) (ZMod r)) *ᵥ v := by
      rw [ht₂]
      exact (u81_sub_diagonal_one v).symm
    have hw0 : Pi.single 0 (v 0) ∈ S :=
      (S.smul_mem_iff h2).1 (e0 ▸ S.sub_mem hv (hSm t₁ v hv))
    have hw1 : Pi.single 1 (v 1) ∈ S :=
      (S.smul_mem_iff h2).1 (e1 ▸ S.sub_mem hv (hSm t₂ v hv))
    have hw2 : Pi.single 2 (v 2) ∈ S :=
      (S.add_mem_iff_right (S.add_mem hw0 hw1)).1
        (Eq.mp (congrArg (· ∈ S) (u81_eq_sum_single v)) hv)
    intro i
    fin_cases i
    exacts [hw0, hw1, hw2]
  have hsmul : ∀ i (c : ZMod r), Pi.single i (1 : ZMod r) ∈ S → Pi.single i c ∈ S := by
    intro i c h
    convert S.smul_mem c h using 1
    ext j
    rcases eq_or_ne j i with rfl | hj <;> simp [*]
  have hkey : ∀ v ∈ S, ∀ i, v i ≠ 0 → Pi.single i (1 : ZMod r) ∈ S := by
    intro v hv i hi
    refine (S.smul_mem_iff hi).1 ?_
    convert hcomp v hv i using 1
    ext j
    rcases eq_or_ne j i with rfl | hj <;> simp [*]
  set I : Finset (Fin 3) := Finset.univ.filter fun i => Pi.single i (1 : ZMod r) ∈ S with hIdef
  have hmemI : ∀ i, i ∈ I ↔ Pi.single i (1 : ZMod r) ∈ S := fun i => by simp [hIdef]
  by_cases hI0 : I = ∅
  · refine Or.inl ((Submodule.eq_bot_iff S).2 fun v hv => ?_)
    by_contra hv0
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
    have := (hmemI i).2 (hkey v hv i hi)
    rw [hI0] at this
    simp at this
  by_cases hIu : I = Finset.univ
  · refine Or.inr (Submodule.eq_top_iff'.2 fun v => ?_)
    have he : ∀ i, Pi.single i (1 : ZMod r) ∈ S := fun i =>
      (hmemI i).1 (by rw [hIu]; exact Finset.mem_univ i)
    refine Eq.mpr (congrArg (· ∈ S) (u81_eq_sum_single v)) ?_
    exact S.add_mem (S.add_mem (hsmul 0 _ (he 0)) (hsmul 1 _ (he 1))) (hsmul 2 _ (he 2))
  refine absurd (fun m hm => ?_) (hU I (Finset.nonempty_iff_ne_empty.2 hI0) hIu)
  set K : Subgroup G := closure (b '' (I : Set (Fin 3)))
  have hcoordS : ∀ w ∈ S, u81Coord b w ∈ K := by
    intro w hw
    have hj : ∀ j, b j ^ (w j).val ∈ K := by
      intro j
      by_cases hwj : w j = 0
      · rw [hwj, ZMod.val_zero, pow_zero]
        exact K.one_mem
      · exact K.pow_mem (subset_closure ⟨j, (hmemI j).2 (hkey w hw j hwj), rfl⟩) _
    exact K.mul_mem (K.mul_mem (hj 0) (hj 1)) (hj 2)
  refine mem_normalizer_fintype fun y hy => ?_
  have hle : K ≤ K.comap (MulAut.conj m).toMonoidHom := by
    refine (closure_le _).2 ?_
    rintro _ ⟨i, hi, rfl⟩
    have h1 := hF.coord_rho_mulVec ⟨m, hm⟩ (Pi.single i 1)
    rw [hF.coord_single_one] at h1
    change m * b i * m⁻¹ ∈ K
    rw [← h1]
    exact hcoordS _ (hSm _ _ ((hmemI i).1 hi))
  exact hle hy

end U81Frame

theorem u81_isStronglyPEmbedded_map {H H' : Type*} [Group H] [Group H'] [Finite H] {p : ℕ}
    [Fact p.Prime] {Y : Subgroup H} (hY : IsStronglyPEmbedded p Y) (f : H →* H')
    (hf : Function.Surjective f) (hkY : f.ker ≤ Y) (hpk : ¬ p ∣ Nat.card f.ker) :
    IsStronglyPEmbedded p (Y.map f) := by
  haveI : Finite H' := Finite.of_surjective f hf
  have hmem : ∀ g, f g ∈ Y.map f → g ∈ Y := fun g hg => by
    obtain ⟨y, hy, hyg⟩ := hg
    have hk : y⁻¹ * g ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyg, inv_mul_cancel]
    simpa using Y.mul_mem hy (hkY hk)
  have hord : ∀ y : H, orderOf y = p → orderOf (f y) = p := fun y hy => by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one]
    · intro h1
      have hyk : y ∈ f.ker := MonoidHom.mem_ker.2 h1
      have := orderOf_dvd_natCard (⟨y, hyk⟩ : f.ker)
      rw [Subgroup.orderOf_mk, hy] at this
      exact hpk this
  refine ⟨fun htop => hY.1 (eq_top_iff.2 fun g _ => hmem g (htop ▸ mem_top _)), ?_, ?_⟩
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hY.2.1
    have hfx := hord x (by rw [Subgroup.orderOf_coe, hx])
    have := orderOf_dvd_natCard (⟨f x, mem_map_of_mem f x.2⟩ : Y.map f)
    rwa [Subgroup.orderOf_mk, hfx] at this
  · intro g' hg' hp
    obtain ⟨g, rfl⟩ := hf g'
    have hg : g ∉ Y := fun h => hg' (mem_map_of_mem f h)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hp
    obtain ⟨y, hy, hyx⟩ := mem_map.1 (mem_inf.1 x.2).1
    obtain ⟨z, hz, hzx⟩ := mem_map.1 (mem_inf.1 x.2).2
    obtain ⟨w, hw, rfl⟩ := mem_map.1 hz
    have hfy : f (g * w * g⁻¹) = f y := by
      rw [hyx, ← hzx]
      simp [MulAut.conj_apply]
    have hfk : f ((g * w * g⁻¹)⁻¹ * y) = 1 := by rw [map_mul, map_inv, hfy, inv_mul_cancel]
    have hk : g⁻¹ * ((g * w * g⁻¹)⁻¹ * y) * g ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, hfk, mul_one, map_inv, inv_mul_cancel]
    have hyc : y ∈ Y.map (MulAut.conj g).toMonoidHom := by
      refine mem_map.2 ⟨w * (g⁻¹ * ((g * w * g⁻¹)⁻¹ * y) * g), Y.mul_mem hw (hkY hk), ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    refine hY.2.2 g hg ?_
    have hpy : p ∣ orderOf y := by
      have h1 := orderOf_map_dvd f y
      rwa [hyx, Subgroup.orderOf_coe, hx] at h1
    have hdvd := orderOf_dvd_natCard
      (⟨y, mem_inf.2 ⟨hy, hyc⟩⟩ : ↥(Y ⊓ Y.map (MulAut.conj g).toMonoidHom))
    rw [Subgroup.orderOf_mk] at hdvd
    exact hpy.trans hdvd

theorem u81_isStronglyPEmbedded_subgroupOf_range {H H' : Type*} [Group H] [Group H'] [Finite H]
    {p : ℕ} [Fact p.Prime] {Y : Subgroup H} (hY : IsStronglyPEmbedded p Y) (f : H →* H')
    (hkY : f.ker ≤ Y) (hpk : ¬ p ∣ Nat.card f.ker) :
    IsStronglyPEmbedded p ((Y.map f).subgroupOf f.range) := by
  have h := u81_isStronglyPEmbedded_map hY f.rangeRestrict f.rangeRestrict_surjective
    (by rwa [MonoidHom.ker_rangeRestrict]) (by rwa [MonoidHom.ker_rangeRestrict])
  convert h using 1
  ext x
  simp [Subgroup.mem_subgroupOf, Subtype.ext_iff, MonoidHom.coe_rangeRestrict]

end CFSG.LocalAnalysis.UniquenessCase.UC22
