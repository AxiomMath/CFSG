module

public import CFSG.LocalAnalysis.WeakClosure81.W15SixA
public import CFSG.LocalAnalysis.WeakClosure81.FiveFiveBase
public import CFSG.LocalAnalysis.WeakClosure81.FiveTenFinal
public import CFSG.LocalAnalysis.WeakClosure81.FiveTenQuotHyp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup

variable {G : Type} [Group G] [Finite G]

structure IsPairAt (M X A : Subgroup G) : Prop where
  A_le : A ≤ X
  A_le_M : A ≤ M
  not_le_ker : ¬ A ≤ kerMOf M X
  maxOver_eq : maxOver X (A ⊔ kerMOf M X) = {M ⊓ X}

theorem IsPair156.toPairAt {M V₀ H A X : Subgroup G} (h : IsPair156 M V₀ H A X) :
    IsPairAt M X A :=
  ⟨h.A_le, h.A_le_M, h.not_le_ker, h.maxOver_eq⟩

private theorem b15_exists_mul {X Y K : Subgroup G} (hYX : Y ≤ X) (hKX : K ≤ X)
    (hKn : (K.subgroupOf X).Normal) (hY : Y ⊔ K = X) {x : G} (hx : x ∈ X) :
    ∃ y ∈ Y, ∃ k ∈ K, x = y * k :=
  exists_mul_of_eq_sup_of_normal (H := X) (X := K) (A := Y) hKX hYX hKn
    (by rw [← hY, sup_comm]) hx

private theorem b15_inf_eq_sup_inf {M X Y K : Subgroup G} (hYX : Y ≤ X) (hKX : K ≤ X)
    (hKM : K ≤ M) (hKn : (K.subgroupOf X).Normal) (hY : Y ⊔ K = X) :
    M ⊓ X = (M ⊓ Y) ⊔ K := by
  refine le_antisymm ?_ (sup_le (le_inf inf_le_left (inf_le_right.trans hYX))
    (le_inf hKM hKX))
  intro x hx
  obtain ⟨hxM, hxX⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨y, hy, k, hk, rfl⟩ := b15_exists_mul hYX hKX hKn hY hxX
  have hyM : y ∈ M := by
    have h1 : y * k * k⁻¹ ∈ M := M.mul_mem hxM (M.inv_mem (hKM hk))
    simpa [mul_assoc] using h1
  exact Subgroup.mul_mem_sup ⟨hyM, hy⟩ hk

private theorem b15_eq_sup_inf {N Y K X : Subgroup G} (hNY : N ≤ Y) (hYX : Y ≤ X)
    (hKX : K ≤ X) (hKn : (K.subgroupOf X).Normal) (hNK : N ⊔ K = X) :
    Y = N ⊔ (Y ⊓ K) := by
  refine le_antisymm ?_ (sup_le hNY inf_le_left)
  intro y hy
  obtain ⟨n, hn, k, hk, hnk⟩ := b15_exists_mul (hNY.trans hYX) hKX hKn
    (by rw [← hNK, sup_comm]) (hYX hy)
  have hkY : k ∈ Y := by
    have h1 : k = n⁻¹ * y := by rw [hnk]; group
    rw [h1]
    exact Y.mul_mem (Y.inv_mem (hNY hn)) hy
  rw [hnk]
  exact Subgroup.mul_mem_sup hn ⟨hkY, hk⟩

private theorem b15_normal_sup_kerMOf {M X Y J : Subgroup G} (hYX : Y ≤ X)
    (hJY_le : J ≤ Y) (hJY : (J.subgroupOf Y).Normal) (hY : Y ⊔ kerMOf M X = X) :
    ((J ⊔ kerMOf M X).subgroupOf X).Normal := by
  have hKX : kerMOf M X ≤ X := kerMOf_le_group M X
  have hKn : ((kerMOf M X).subgroupOf X).Normal := normal_subgroupOf_kerMOf M X
  have hKnorm : X ≤ Subgroup.normalizer ((kerMOf M X : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).1 hKn
  have hJnorm : Y ≤ Subgroup.normalizer ((J : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJY_le).1 hJY
  rw [Subgroup.normal_subgroupOf_iff (sup_le (hJY_le.trans hYX) hKX)]
  intro n x hn hx
  obtain ⟨y, hy, k, hk, rfl⟩ := b15_exists_mul hYX hKX hKn hY hx
  have hkconj : k * n * k⁻¹ ∈ J ⊔ kerMOf M X := by
    have hmap : (J ⊔ kerMOf M X).map (MulAut.conj k).toMonoidHom ≤ J ⊔ kerMOf M X := by
      rw [Subgroup.map_sup _ _ _]
      have hKconj : (kerMOf M X).map (MulAut.conj k).toMonoidHom = kerMOf M X :=
        Subgroup.mem_normalizer_iff_map_conj_eq.1 (hKnorm (hKX hk))
      rw [hKconj]
      refine sup_le ?_ le_sup_right
      intro m hm
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hm
      change k * j * k⁻¹ ∈ J ⊔ kerMOf M X
      have hjY : j ∈ Y := hJY_le hj
      have hjX : j ∈ X := hYX hjY
      have hkj : j⁻¹ * k * j * k⁻¹ ∈ kerMOf M X := by
        have h1 : j⁻¹ * k * j ∈ kerMOf M X := by
          have h := conj_mem_kerMOf (M := M) (H := X) (Subgroup.inv_mem _ hjX) hk
          simpa [mul_assoc] using h
        exact Subgroup.mul_mem (kerMOf M X) h1 (Subgroup.inv_mem _ hk)
      have heq : k * j * k⁻¹ = j * (j⁻¹ * k * j * k⁻¹) := by group
      rw [heq]
      exact Subgroup.mul_mem_sup hj hkj
    exact hmap (Subgroup.mem_map.2 ⟨n, hn, rfl⟩)
  have hyconj : y * (k * n * k⁻¹) * y⁻¹ ∈ J ⊔ kerMOf M X := by
    have hmap : (J ⊔ kerMOf M X).map (MulAut.conj y).toMonoidHom ≤ J ⊔ kerMOf M X := by
      rw [Subgroup.map_sup _ _ _]
      have hJconj : J.map (MulAut.conj y).toMonoidHom = J :=
        Subgroup.mem_normalizer_iff_map_conj_eq.1 (hJnorm hy)
      have hKconj : (kerMOf M X).map (MulAut.conj y).toMonoidHom = kerMOf M X :=
        Subgroup.mem_normalizer_iff_map_conj_eq.1 (hKnorm (hYX hy))
      rw [hJconj, hKconj]
    exact hmap (Subgroup.mem_map.2 ⟨k * n * k⁻¹, hkconj, rfl⟩)
  have heq : y * k * n * (y * k)⁻¹ = y * (k * n * k⁻¹) * y⁻¹ := by group
  rw [heq]
  exact hyconj

namespace IsPairAt

variable {M X A : Subgroup G}

theorem not_le_M (h : IsPairAt M X A) : ¬ X ≤ M := by
  have hmem : M ⊓ X ∈ maxOver X (A ⊔ kerMOf M X) := by
    rw [h.maxOver_eq]
    exact Set.mem_singleton _
  have hlt : M ⊓ X < X := hmem.1.1
  intro hXM
  exact (ne_of_lt hlt) (le_antisymm hlt.le (le_inf hXM le_rfl))

theorem le_M_of_proper (h : IsPairAt M X A) {N : Subgroup G} (hNX : N ≤ X) (hN : N ≠ X)
    (hAN : A ≤ N) (hKN : kerMOf M X ≤ N) : N ≤ M := by
  have hlt : N < X := lt_of_le_of_ne hNX hN
  obtain ⟨N', hN'max, hNN'⟩ := exists_isMaxSubgroupIn hlt
  have hmem : N' ∈ maxOver X (A ⊔ kerMOf M X) :=
    ⟨hN'max, sup_le (hAN.trans hNN') (hKN.trans hNN')⟩
  rw [h.maxOver_eq, Set.mem_singleton_iff] at hmem
  calc N ≤ N' := hNN'
    _ = M ⊓ X := hmem
    _ ≤ M := inf_le_left

theorem restrict (h : IsPairAt M X A) {Y : Subgroup G} (hYX : Y ≤ X) (hAY : A ≤ Y)
    (hY : Y ⊔ kerMOf M X = X) :
    kerMOf M Y = Y ⊓ kerMOf M X ∧ IsPairAt M Y A := by
  have hKX : kerMOf M X ≤ X := kerMOf_le_group M X
  have hKM : kerMOf M X ≤ M := kerMOf_le_left M X
  have hKn : ((kerMOf M X).subgroupOf X).Normal := normal_subgroupOf_kerMOf M X
  have hJKnormal : ((kerMOf M Y ⊔ kerMOf M X).subgroupOf X).Normal :=
    b15_normal_sup_kerMOf hYX (kerMOf_le_group M Y) (normal_subgroupOf_kerMOf M Y) hY
  have hker : kerMOf M Y = Y ⊓ kerMOf M X := by
    refine le_antisymm ?_ ?_
    · intro j hj
      refine Subgroup.mem_inf.2 ⟨kerMOf_le_group M Y hj, ?_⟩
      exact le_kerMOf_of_normal (M := M) (H := X) (N := kerMOf M Y ⊔ kerMOf M X)
        (sup_le ((kerMOf_le_group M Y).trans hYX) hKX) hJKnormal
        (sup_le (kerMOf_le_left M Y) hKM) (Subgroup.mem_sup_left hj)
    · have hinfnorm : ((Y ⊓ kerMOf M X).subgroupOf Y).Normal := by
        rw [Subgroup.normal_subgroupOf_iff inf_le_left]
        intro a b ha hb
        obtain ⟨haY, haK⟩ := Subgroup.mem_inf.1 ha
        exact Subgroup.mem_inf.2 ⟨Y.mul_mem (Y.mul_mem hb haY) (Y.inv_mem hb),
          conj_mem_kerMOf (hYX hb) haK⟩
      intro x hx
      exact le_kerMOf_of_normal (M := M) (H := Y) (N := Y ⊓ kerMOf M X)
        inf_le_left hinfnorm (inf_le_right.trans hKM) hx
  have hMmax : IsMaxSubgroupIn X (M ⊓ X) := by
    have hmem : M ⊓ X ∈ maxOver X (A ⊔ kerMOf M X) := by
      rw [h.maxOver_eq]
      exact Set.mem_singleton _
    exact hmem.1
  have hMYlt : M ⊓ Y < Y := by
    refine lt_of_le_of_ne inf_le_right ?_
    intro heq
    exact h.not_le_M (by rw [← hY]; exact sup_le (heq.ge.trans inf_le_left) hKM)
  have hMYmem : M ⊓ Y ∈ maxOver Y (A ⊔ (Y ⊓ kerMOf M X)) := by
    refine ⟨⟨hMYlt, ?_⟩, ?_⟩
    · intro L hML hLY
      have hMXL : M ⊓ X = (M ⊓ Y) ⊔ kerMOf M X :=
        b15_inf_eq_sup_inf hYX hKX hKM hKn hY
      have hlt : (M ⊓ Y) ⊔ kerMOf M X < L ⊔ kerMOf M X := by
        refine lt_of_le_of_ne (sup_le (hML.le.trans le_sup_left) le_sup_right) ?_
        intro heq
        have hLM : L ≤ M := by
          have h1 : L ≤ (M ⊓ Y) ⊔ kerMOf M X := le_sup_left.trans heq.symm.le
          exact h1.trans (sup_le inf_le_left hKM)
        exact (not_le_of_gt hML) (le_inf hLM hLY)
      have hsupX : L ⊔ kerMOf M X = X :=
        hMmax.2 _ (hMXL ▸ hlt) (sup_le (hLY.trans hYX) hKX)
      have hYeq : Y = L ⊔ (Y ⊓ kerMOf M X) :=
        b15_eq_sup_inf hLY hYX hKX hKn hsupX
      have hYKL : Y ⊓ kerMOf M X ≤ L :=
        (le_inf (inf_le_right.trans hKM) inf_le_left).trans hML.le
      exact (hYeq.trans (sup_eq_left.2 hYKL)).symm
    · exact sup_le (le_inf h.A_le_M hAY)
        (le_inf (inf_le_right.trans hKM) inf_le_left)
  refine ⟨hker, hAY, h.A_le_M, ?_, ?_⟩
  · intro hle
    rw [hker] at hle
    exact h.not_le_ker (hle.trans inf_le_right)
  · rw [hker]
    ext N
    constructor
    · intro hN
      rw [Set.mem_singleton_iff]
      have hNYK : N ⊔ kerMOf M X ≠ X := by
        intro heq
        have h3 : Y = N ⊔ (Y ⊓ kerMOf M X) :=
          b15_eq_sup_inf hN.1.1.le hYX hKX hKn heq
        have hle : Y ⊓ kerMOf M X ≤ N :=
          (le_sup_right : Y ⊓ kerMOf M X ≤ A ⊔ (Y ⊓ kerMOf M X)).trans hN.2
        have hYN : Y = N := h3.trans (sup_eq_left.2 hle)
        exact (ne_of_gt hN.1.1) hYN
      have hNM : N ≤ M := by
        have h1 : N ⊔ kerMOf M X ≤ M :=
          h.le_M_of_proper (N := N ⊔ kerMOf M X)
            (sup_le (hN.1.1.le.trans hYX) hKX) hNYK
            ((le_sup_left : A ≤ A ⊔ (Y ⊓ kerMOf M X)).trans (hN.2.trans le_sup_left))
            le_sup_right
        exact le_sup_left.trans h1
      have hNMY : N ≤ M ⊓ Y := le_inf hNM hN.1.1.le
      rcases eq_or_lt_of_le hNMY with heq | hlt
      · exact heq
      · exact absurd (hN.1.2 (M ⊓ Y) hlt inf_le_right) (ne_of_lt hMYlt)
    · intro hN
      rw [Set.mem_singleton_iff] at hN
      rw [hN]
      exact hMYmem

theorem le_M_of_isSylowIn (h : IsPairAt M X A) {P : Subgroup G} (hP : IsSylowIn 2 P X)
    (hAP : A ≤ P) : P ≤ M := by
  have hKX : kerMOf M X ≤ X := kerMOf_le_group M X
  by_cases hPK : P ⊔ kerMOf M X = X
  · exfalso
    have hKn : ((kerMOf M X).subgroupOf X).Normal := normal_subgroupOf_kerMOf M X
    have hlift_top : kerQuotLift M X (⊤ : Subgroup (KerQuot M X)) = X := by
      ext x
      rw [mem_kerQuotLift_iff]
      exact ⟨fun ⟨hx, _⟩ => hx, fun hx => ⟨hx, Subgroup.mem_top _⟩⟩
    have hXtop : kerQuotImg M X X = ⊤ := by
      have h := kerQuotImg_kerQuotLift M X (⊤ : Subgroup (KerQuot M X))
      rwa [hlift_top] at h
    have hPtop : kerQuotImg M X P = ⊤ := by
      have h2 := kerQuotLift_kerQuotImg (M := M) (H := X) (X := P) hP.le
      rw [hPK] at h2
      have h3 := kerQuotImg_kerQuotLift M X (kerQuotImg M X P)
      rw [h2] at h3
      rw [hXtop] at h3
      exact h3.symm
    have hQ2sub : IsPGroup 2 (⊤ : Subgroup (KerQuot M X)) := by
      have h := (isSylowIn_kerQuotImg (M := M) (H := X) hP).isPGroup
      rwa [hPtop] at h
    have hQ2 : IsPGroup 2 (KerQuot M X) := hQ2sub.of_equiv Subgroup.topEquiv
    haveI : Group.IsNilpotent (KerQuot M X) := hQ2.isNilpotent
    have hcoat : IsCoatom (kerQuotImg M X M) := by
      have hmem : kerQuotImg M X M ∈ maxOver ⊤ (kerQuotImg M X A) := by
        rw [maxOver_kerQuotImg_of_inf h.A_le h.maxOver_eq]
        exact Set.mem_singleton _
      obtain ⟨hlt, hmax⟩ := hmem.1
      exact ⟨ne_of_lt hlt, fun b hb => hmax b hb le_top⟩
    have hMstar_norm : (kerQuotImg M X M).Normal :=
      (Group.normalizerCondition_of_isNilpotent (G := KerQuot M X)).normal_of_coatom
        (kerQuotImg M X M) hcoat
    have hMnorm : ((M ⊓ X).subgroupOf X).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
      intro x hx
      rw [← kerQuotLift_kerQuotImg_left M X]
      refine mem_normalizer_kerQuotLift hx ?_
      rw [show Subgroup.normalizer
          ((kerQuotImg M X M : Subgroup (KerQuot M X)) : Set (KerQuot M X)) = ⊤
        from Subgroup.normalizer_eq_top_iff.mpr hMstar_norm]
      exact Subgroup.mem_top _
    have hle : M ⊓ X ≤ kerMOf M X :=
      le_kerMOf_of_normal (M := M) (H := X) (N := M ⊓ X) inf_le_right hMnorm inf_le_left
    exact h.not_le_ker ((le_inf h.A_le_M h.A_le).trans hle)
  · exact le_sup_left.trans
      (h.le_M_of_proper (sup_le hP.le hKX) hPK (hAP.trans le_sup_left) le_sup_right)

theorem odd_relIndex (h : IsPairAt M X A) (hA : IsPGroup 2 A) : Odd (M.relIndex X) := by
  obtain ⟨P, hP, hAP⟩ := exists_isSylowIn_ge 2 h.A_le hA
  have hPM : P ≤ M := h.le_M_of_isSylowIn hP hAP
  have hPle : P ≤ M ⊓ X := le_inf hPM hP.le
  have hrel := Subgroup.relIndex_mul_relIndex (H := P) (K := M ⊓ X) (L := X) hPle
    (inf_le_right : M ⊓ X ≤ X)
  rw [Subgroup.inf_relIndex_right] at hrel
  have hodd : Odd (P.relIndex X) :=
    Nat.not_even_iff_odd.mp fun he => hP.not_dvd_relIndex (even_iff_two_dvd.mp he)
  rw [← hrel] at hodd
  exact (Nat.odd_mul.mp hodd).2

theorem sec5Hyp (h : IsPairAt M X A) (hA : IsElemAbelian 2 A) : Sec5Hyp X M A :=
  ⟨hA, h.A_le, h.A_le_M, h.not_le_M, h.odd_relIndex hA.isPGroup⟩

end IsPairAt

end CFSG.LocalAnalysis.WeakClosure81
