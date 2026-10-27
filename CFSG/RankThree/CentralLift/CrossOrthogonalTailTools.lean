module

public import CFSG.RankThree.CentralLift.CrossOrthogonalSplit
public import CFSG.RankThree.CentralLiftSO.TailWeyl
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailSubspaceCount

public section

namespace CFSG.RankThree.CentralLift

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial (orthElementaryGroup orthogonal_elementary_perfect)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.ComponentInitial.NormTail
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit (eps flag mem_flag_iff_coord coordWt
  coordWt_inl signedPermAut signedPermAut_eps posRoots)
open CFSG.RankThree.CentralLiftSO.TailO (TailHyp liftWeyl weylHom apply_hypVec_weylHom
  weylHom_surjective map_conj_tailRootGroup_weylHom)

variable {K L : Type} [Field K] [Field L] [Algebra K L] {T : NormTailData K L} {r : ℕ}

theorem weylHom_eq_one_of_mem_tailBorel {E : Type*} [Group E] [Finite E] {π : E →* G0 T r}
    (hS : TailHyp T π) (v : liftWeyl T π)
    (hv : ((π v : G0 T r) : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) ∈
      tailBorel r (normForm T)) :
    weylHom hS v = 1 := by
  obtain ⟨-, hflag⟩ := mem_tailBorel.1 hv
  have key : ∀ j : Fin r, ∃ m : Fin r, m ≤ j ∧
      ((weylHom hS v : weylGroupB r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) (eps r j) = eps r m := by
    intro j
    obtain ⟨μ, c', hgc, hc'⟩ := apply_hypVec_weylHom hS v (Sum.inl j)
    have hmem : ((π v : G0 T r) : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L))
        (hypVec K L (Sum.inl j)) ∈ tailFlag K L r (j + 1) := by
      rw [← hflag (j + 1) (by omega) (by have := j.isLt; omega)]
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨j, Nat.lt_succ_self _, rfl⟩)
    rw [hgc, mem_tailFlag_iff, mem_flag_iff_coord] at hmem
    rcases c' with m | m
    · refine ⟨m, ?_, ?_⟩
      · by_contra hlt
        have h0 := hmem.1.2 m (by rw [Fin.not_le] at hlt; exact hlt)
        simp only [hypVec, Prod.smul_fst, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
          mul_one] at h0
        exact μ.ne_zero h0
      · rw [← coordWt_inl, ← hc', coordWt_inl]
    · exfalso
      have h0 := hmem.1.1 m
      simp only [hypVec, Prod.smul_fst, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
        mul_one] at h0
      exact μ.ne_zero h0
  choose m hm hmw using key
  have hinj : Function.Injective m := by
    intro a b hab
    have h1 : ((weylHom hS v : weylGroupB r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) (eps r a) =
        ((weylHom hS v : weylGroupB r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) (eps r b) := by
      rw [hmw, hmw, hab]
    have h2 := ((weylHom hS v : weylGroupB r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)).injective h1
    have h3 := congrFun h2 a
    simp only [eps, Pi.single_eq_same] at h3
    by_contra hne
    rw [Pi.single_eq_of_ne hne] at h3
    exact one_ne_zero h3
  have hbij : Function.Bijective m := Finite.injective_iff_bijective.1 hinj
  have hperm : Equiv.ofBijective m hbij = 1 :=
    LinearRoots.perm_eq_one_of_forall_le fun a => hm a
  have hmid : ∀ j, m j = j := fun j => by
    have := congrArg (fun τ : Equiv.Perm (Fin r) => τ j) hperm
    simpa using this
  refine Subtype.ext ?_
  change ((weylHom hS v : weylGroupB r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) =
    LinearEquiv.refl ℤ (Fin r → ℤ)
  refine (Pi.basisFun ℤ (Fin r)).ext' fun j => ?_
  rw [Pi.basisFun_apply, LinearEquiv.refl_apply]
  change ((weylHom hS v : weylGroupB r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) (eps r j) = eps r j
  rw [hmw, hmid]

theorem exists_weylGroupB_neg {β : Fin r → ℤ} (hβ : β ∈ posRootsB r) :
    ∃ w ∈ weylGroupB r, w β = -β := by
  rcases hβ with ⟨i, rfl⟩ | hβ
  · set δ : Fin r → ℤˣ := Pi.mulSingle i (-1) with hδ
    refine ⟨signedPermAut r 1 δ, signedPermAut_mem_weylGroupB 1 δ, ?_⟩
    rw [signedPermAut_eps, hδ, Pi.mulSingle_eq_same]
    simp
  · obtain ⟨w, ⟨σ, δ, -, rfl⟩, hw⟩ := exists_weylGroup_neg hβ
    exact ⟨signedPermAut r σ δ, signedPermAut_mem_weylGroupB σ δ, hw⟩

theorem sup_map_eq_top_tail {E : Type*} [Group E] [Finite E] {π : E →* G0 T r}
    (hS : TailHyp T π) {B : Subgroup E}
    (hU : ∀ u ∈ tailUnipotent r (normForm T), ∃ b ∈ B, ((π b : G0 T r) :
      ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) = u) :
    B.map π ⊔ (liftWeyl T π).map π = ⊤ := by
  set S := B.map π ⊔ (liftWeyl T π).map π with hSdef
  set S' := S.map (orthElementaryGroup (quadTail r (normForm T))).subtype with hS'
  have hBS : ∀ b ∈ B, ((π b : G0 T r) :
      ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) ∈ S' := fun b hb =>
    ⟨π b, Subgroup.mem_sup_left ⟨b, hb, rfl⟩, rfl⟩
  have hNS : ∀ v ∈ liftWeyl T π, ((π v : G0 T r) :
      ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) ∈ S' := fun v hv =>
    ⟨π v, Subgroup.mem_sup_right ⟨v, hv, rfl⟩, rfl⟩
  have hpos : ∀ β ∈ posRootsB r, tailRootGroup r (normForm T) β ≤ S' := fun β hβ x hx => by
    obtain ⟨b, hb, rfl⟩ := hU x (tailRootGroup_le_tailUnipotent hβ hx)
    exact hBS b hb
  have hroot : ∀ α ∈ rootsB r, tailRootGroup r (normForm T) α ≤ S' := by
    intro α hα
    rcases (mem_posRootsB_or_neg_mem_posRootsB hα).1 with hαp | hnα
    · exact hpos α hαp
    · obtain ⟨w, hw, hwα⟩ := exists_weylGroupB_neg hnα
      obtain ⟨v, hv⟩ := weylHom_surjective hS ⟨w, hw⟩
      have hmap := map_conj_tailRootGroup_weylHom hS v (posRootsB_subset_rootsB hnα)
      rw [hv] at hmap
      change _ = tailRootGroup r (normForm T) (w (-α)) at hmap
      rw [hwα, neg_neg] at hmap
      rw [← hmap]
      rintro _ ⟨y, hy, rfl⟩
      exact mul_mem (mul_mem (hNS v v.2) (hpos _ hnα hy)) (inv_mem (hNS v v.2))
  have hsup : tailRootSupr r (normForm T) ≤ S' := iSup₂_le hroot
  rw [eq_top_iff]
  intro g _
  have hg : ((g : G0 T r) : ((Fin r ⊕ Fin r → K) × L) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × L)) ∈
      tailRootSupr r (normForm T) := by
    rw [← (orthogonal_geometry_tail_root_generation (normForm_anisotropic T)
      ⟨1, one_ne_zero⟩).1]
    exact g.2
  obtain ⟨t, ht, hteq⟩ := hsup hg
  rwa [Subtype.ext hteq] at ht

theorem isPerfect_G0 [FiniteDimensional K L] (hr : 3 ≤ r)
    (hreg : (polarBilin (normForm T)).Nondegenerate) : Group.IsPerfect (G0 T r) :=
  (orthogonal_elementary_perfect (nondegenerate_polarBilin_quadTail hreg)
    ⟨tailFlag K L r 3, finrank_tailFlag hr, fun _ hx => quadTail_eq_zero_of_mem_tailFlag hx⟩).1

theorem nondegenerate_polarBilin_normForm_of_two_ne_zero (h2 : (2 : K) ≠ 0) :
    (polarBilin (normForm T)).Nondegenerate :=
  nondegenerate_polarBilin_of_forall fun z hz => by
    have h := hz z
    rw [polar_self_eq_two_mul] at h
    exact normForm_anisotropic T z ((mul_eq_zero.1 h).resolve_left h2)

end CFSG.RankThree.CentralLift
