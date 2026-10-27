module

public import CFSG.LocalAnalysis.WeakClosure81.W16QExcL2
public import CFSG.GroupTheory.PowMemSupOfPGroup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

private theorem w16q_relIndex_sup_eq_of_le_normalizer {H K : Subgroup G}
    (hHK : H ≤ normalizer (K : Set G)) : K.relIndex (H ⊔ K) = K.relIndex H := by
  set N : Subgroup G := normalizer (K : Set G) with hN
  have hH : H ≤ N := hHK
  have hK : K ≤ N := Subgroup.le_normalizer
  haveI : (K.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h : (K.subgroupOf N).relIndex ((H.subgroupOf N) ⊔ (K.subgroupOf N)) =
      (K.subgroupOf N).relIndex (H.subgroupOf N) :=
    Subgroup.relIndex_sup_right (H.subgroupOf N) (K.subgroupOf N)
  rw [← Subgroup.subgroupOf_sup hH hK,
    Subgroup.relIndex_subgroupOf (H := K) (K := H ⊔ K) (L := N) (sup_le hH hK),
    Subgroup.relIndex_subgroupOf (H := K) (K := H) (L := N) hH] at h
  exact h

private theorem w16q_relIndex_sup_eq_self_of_le_normalizer {H K : Subgroup G}
    (hHK : H ≤ normalizer (K : Set G)) : H.relIndex (H ⊔ K) = H.relIndex K := by
  haveI : K.IsFiniteRelIndex H := Subgroup.isFiniteRelIndex_of_finiteIndex
  have h1 := Subgroup.relIndex_inf_mul_relIndex (H := H) (K := K) (L := H ⊔ K)
  rw [inf_eq_left.2 le_sup_right] at h1
  have h2 := Subgroup.relIndex_mul_relIndex (H := H ⊓ K) (K := H) (L := H ⊔ K)
    inf_le_left le_sup_left
  rw [Subgroup.inf_relIndex_left] at h2
  have h3 : K.relIndex (H ⊔ K) = K.relIndex H :=
    w16q_relIndex_sup_eq_of_le_normalizer hHK
  rw [h3] at h1
  have hne : K.relIndex H ≠ 0 := Subgroup.relIndex_ne_zero (H := K) (K := H)
  have heq : K.relIndex H * H.relIndex K = K.relIndex H * H.relIndex (H ⊔ K) := by
    have h := h1.trans h2.symm
    rwa [mul_comm (H.relIndex K) (K.relIndex H)] at h
  exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) heq).symm

private theorem w16q_normalizer_centralizer_le (V : Subgroup G) :
    normalizer (V : Set G) ≤ normalizer (centralizer (V : Set G) : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
      (H := centralizer (V : Set G)) (K := normalizer (V : Set G))
      (Subgroup.centralizer_le_normalizer (V : Set G))).mp
    (inferInstance : ((centralizer (V : Set G)).subgroupOf
      (normalizer (V : Set G))).Normal)

namespace Exc1616

variable {M V₀ V U S H : Subgroup G}
  {φ : ↥(conjClosure V H) →* PSL(2, GaloisField 2 (E3.mQuot V (iSub16 V H)))}

theorem qSub16_le_tSub16 (e : Exc1616 M V₀ V U S H φ) : qSub16 V₀ V S H ≤ tSub16 V₀ S := by
  have c := e.cfg
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : tSub16 V₀ S ≤ H := inf_le_left.trans c.min.fam16.1
  have hTN : tSub16 V₀ S ≤ normalizer (conjClosure V H : Set G) :=
    hTH.trans (le_normalizer_conjClosure V H)
  have hT2 : IsPGroup 2 (tSub16 V₀ S) := c.cex.sylow.isPGroup.to_le inf_le_left
  have hle : V ⊔ iSub16 V H ≤ tSub16 V₀ S ⊓ conjClosure V H :=
    le_inf (sup_le c.V_le_tSub16 c.iSub16_le_tSub16)
      (sup_le (le_conjClosure V H) c.iSub16_le_conjClosure)
  have hdiv : (tSub16 V₀ S ⊓ conjClosure V H).relIndex (conjClosure V H) ∣
      (V ⊔ iSub16 V H).relIndex (conjClosure V H) :=
    ⟨(V ⊔ iSub16 V H).relIndex (tSub16 V₀ S ⊓ conjClosure V H), by
      rw [mul_comm]
      exact (Subgroup.relIndex_mul_relIndex (H := V ⊔ iSub16 V H)
        (K := tSub16 V₀ S ⊓ conjClosure V H) (L := conjClosure V H) hle inf_le_right).symm⟩
  have hTodd : ¬ 2 ∣ (tSub16 V₀ S).relIndex (conjClosure V H ⊔ tSub16 V₀ S) := by
    rw [sup_comm (conjClosure V H) (tSub16 V₀ S)]
    rw [w16q_relIndex_sup_eq_self_of_le_normalizer hTN, ← Subgroup.inf_relIndex_right]
    intro hd
    exact e.isSylowIn_sup.not_dvd_relIndex (hd.trans hdiv)
  have hSylT : IsSylowIn 2 (tSub16 V₀ S) (conjClosure V H ⊔ tSub16 V₀ S) :=
    ⟨le_sup_right, hT2, hTodd⟩
  exact CFSG.Quasithin.pCoreOf_le_of_isSylowIn hSylT

theorem qSub16_inf_le (e : Exc1616 M V₀ V U S H φ) :
    qSub16 V₀ V S H ⊓ conjClosure V H ≤ iSub16 V H := by
  have c := e.cfg
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 (qSub16 V₀ V S H) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (conjClosure V H ⊔ tSub16 V₀ S)
  have hKnormQ : conjClosure V H ≤ normalizer (qSub16 V₀ V S H : Set G) :=
    c.conjClosure_le_H.trans c.le_normalizer_qSub16
  have hKnorm : conjClosure V H ≤
      normalizer ((qSub16 V₀ V S H ⊓ conjClosure V H : Subgroup G) : Set G) :=
    (le_inf hKnormQ (le_normalizer (H := conjClosure V H))).trans
      (inf_normalizer_le_normalizer_inf (H := qSub16 V₀ V S H)
        (K := conjClosure V H))
  haveI hNnorm : ((qSub16 V₀ V S H ⊓ conjClosure V H).subgroupOf
      (conjClosure V H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hKnorm
  have hN2 : IsPGroup 2 ((qSub16 V₀ V S H ⊓ conjClosure V H).subgroupOf
      (conjClosure V H)) :=
    (hQ2.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  haveI hmapN : (((qSub16 V₀ V S H ⊓ conjClosure V H).subgroupOf
      (conjClosure V H)).map φ).Normal :=
    Subgroup.Normal.map hNnorm φ e.surj
  have hbot : ((qSub16 V₀ V S H ⊓ conjClosure V H).subgroupOf
      (conjClosure V H)).map φ = ⊥ :=
    eq_bot_of_normal_of_isPGroup_of_isL2Pair e.isL2Pair_map (hN2.map φ)
  have hker : (qSub16 V₀ V S H ⊓ conjClosure V H).subgroupOf (conjClosure V H) ≤ φ.ker := by
    intro x hx
    have hxmap : φ x ∈ (((qSub16 V₀ V S H ⊓ conjClosure V H).subgroupOf
        (conjClosure V H)).map φ) := Subgroup.mem_map_of_mem φ hx
    rw [hbot] at hxmap
    simpa using hxmap
  intro x hx
  have hx' : (⟨x, hx.2⟩ : ↥(conjClosure V H)) ∈ φ.ker :=
    hker (Subgroup.mem_subgroupOf.mpr hx)
  rw [e.ker] at hx'
  simpa only [Subgroup.mem_subgroupOf] using hx'

theorem comm_mem_qSub16 (e : Exc1616 M V₀ V U S H φ) {x k : G} (hx : x ∈ qSub16 V₀ V S H)
    (hk : k ∈ conjClosure V H) : k * x * k⁻¹ * x⁻¹ ∈ iSub16 V H := by
  have c := e.cfg
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxH : x ∈ H := c.sup_le_H (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx)
  have hkH : k ∈ H := c.conjClosure_le_H hk
  have h1 : k * x * k⁻¹ ∈ qSub16 V₀ V S H :=
    (Subgroup.mem_normalizer_iff.mp (c.le_normalizer_qSub16 hkH) x).1 hx
  have h2 : x * k⁻¹ * x⁻¹ ∈ conjClosure V H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V H hxH) k⁻¹).1
      ((conjClosure V H).inv_mem hk)
  have h3 : k * x * k⁻¹ * x⁻¹ ∈ qSub16 V₀ V S H :=
    (qSub16 V₀ V S H).mul_mem h1 ((qSub16 V₀ V S H).inv_mem hx)
  have h4 : k * x * k⁻¹ * x⁻¹ ∈ conjClosure V H := by
    have h := (conjClosure V H).mul_mem hk h2
    rwa [show k * (x * k⁻¹ * x⁻¹) = k * x * k⁻¹ * x⁻¹ by group] at h
  exact qSub16_inf_le e ⟨h3, h4⟩

theorem mul_self_mem_centralizer (e : Exc1616 M V₀ V U S H φ) {y : G}
    (hy : y ∈ qSub16 V₀ V S H) : y * y ∈ centralizer (conjClosure V H : Set G) := by
  have c := e.cfg
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQT := qSub16_le_tSub16 e
  have hQC : qSub16 V₀ V S H ≤ centralizer (iSub16 V H : Set G) :=
    c.qSub16_le_centralizer hQT
  have hI2 : IsElemAbelian 2 (iSub16 V H) :=
    Cex16.isElemAbelian_iSub16 c.one c.std c.cex c.min.fam16
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hj : k * y * k⁻¹ * y⁻¹ ∈ iSub16 V H := comm_mem_qSub16 e hy hk
  have hjy : (k * y * k⁻¹ * y⁻¹) * y = y * (k * y * k⁻¹ * y⁻¹) :=
    Subgroup.mem_centralizer_iff.mp (hQC hy) _ hj
  have hjj : (k * y * k⁻¹ * y⁻¹) * (k * y * k⁻¹ * y⁻¹) = 1 := by
    have h := hI2.2 _ hj
    simpa [pow_two] using h
  have hfix : k * (y * y) * k⁻¹ = y * y := by
    calc k * (y * y) * k⁻¹ = (k * y * k⁻¹) * (k * y * k⁻¹) := by group
      _ = ((k * y * k⁻¹ * y⁻¹) * y) * ((k * y * k⁻¹ * y⁻¹) * y) := by group
      _ = (k * y * k⁻¹ * y⁻¹) * (y * (k * y * k⁻¹ * y⁻¹)) * y := by group
      _ = (k * y * k⁻¹ * y⁻¹) * ((k * y * k⁻¹ * y⁻¹) * y) * y := by rw [hjy]
      _ = ((k * y * k⁻¹ * y⁻¹) * (k * y * k⁻¹ * y⁻¹)) * (y * y) := by group
      _ = y * y := by rw [hjj, one_mul]
  calc k * (y * y) = (k * (y * y) * k⁻¹) * k := by group
    _ = (y * y) * k := by rw [hfix]

theorem inf_centralizer_le_iSub16 (e : Exc1616 M V₀ V U S H φ) :
    conjClosure V H ⊓ centralizer (iSub16 V H : Set G) ≤ iSub16 V H := by
  have c := e.cfg
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 c.cex.hyp.ne_bot
  have hwV : (w : G) ∈ V₀ := w.2
  have hw1' : (w : G) ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hV₀I : V₀ ≤ iSub16 V H := le_sup_right.trans c.le_iSub16
  have hleM : conjClosure V H ⊓ centralizer (iSub16 V H : Set G) ≤ M := by
    intro x hx
    exact c.cex.hyp.centralizer_le hwV hw1'
      (Subgroup.centralizer_le (Set.singleton_subset_iff.2 (hV₀I hwV)) hx.2)
  have hKnormI : conjClosure V H ≤ normalizer (iSub16 V H : Set G) :=
    c.conjClosure_le_H.trans (le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H)
  have hKnormC : conjClosure V H ≤
      normalizer (centralizer (iSub16 V H : Set G) : Set G) :=
    hKnormI.trans (w16q_normalizer_centralizer_le (iSub16 V H))
  have hKnorm : conjClosure V H ≤
      normalizer ((conjClosure V H ⊓ centralizer (iSub16 V H : Set G) : Subgroup G) : Set G) :=
    (le_inf (le_normalizer (H := conjClosure V H)) hKnormC).trans
      (inf_normalizer_le_normalizer_inf (H := conjClosure V H)
        (K := centralizer (iSub16 V H : Set G)))
  haveI hNnorm : ((conjClosure V H ⊓ centralizer (iSub16 V H : Set G)).subgroupOf
      (conjClosure V H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hKnorm
  have hVK : V ≤ conjClosure V H := le_conjClosure V H
  have hsub_le_norm : ((conjClosure V H ⊓ M).subgroupOf (conjClosure V H)) ≤
      normalizer ((V.subgroupOf (conjClosure V H)) : Subgroup ↥(conjClosure V H)) := by
    rw [← Subgroup.subgroupOf_normalizer_eq (H := V) (N := conjClosure V H) hVK,
      c.cex.hyp.h6.normalizer_eq]
    exact Subgroup.subgroupOf_mono (conjClosure V H) inf_le_right
  have hmap_le : ((conjClosure V H ⊓ centralizer (iSub16 V H : Set G)).subgroupOf
      (conjClosure V H)).map φ ≤
      normalizer (((V.subgroupOf (conjClosure V H)).map φ) : Subgroup _) :=
    (Subgroup.map_mono (Subgroup.subgroupOf_mono (conjClosure V H)
      (le_inf inf_le_left hleM))).trans
      ((Subgroup.map_mono hsub_le_norm).trans (Subgroup.le_normalizer_map φ))
  haveI hmapNorm : (((conjClosure V H ⊓ centralizer (iSub16 V H : Set G)).subgroupOf
      (conjClosure V H)).map φ).Normal := Subgroup.Normal.map hNnorm φ e.surj
  have hbot := eq_bot_of_normal_le_normalizer_of_isL2Pair e.isL2Pair_map hmap_le
  have hker : (conjClosure V H ⊓ centralizer (iSub16 V H : Set G)).subgroupOf
      (conjClosure V H) ≤ φ.ker := by
    intro x hx
    have hxmap : φ x ∈ (((conjClosure V H ⊓ centralizer (iSub16 V H : Set G)).subgroupOf
        (conjClosure V H)).map φ) := Subgroup.mem_map_of_mem φ hx
    rw [hbot] at hxmap
    simpa using hxmap
  intro x hx
  have hx' : (⟨x, hx.1⟩ : ↥(conjClosure V H)) ∈ φ.ker :=
    hker (Subgroup.mem_subgroupOf.mpr hx)
  rw [e.ker] at hx'
  simpa only [Subgroup.mem_subgroupOf] using hx'

theorem tSub16_inf_centralizer_le (e : Exc1616 M V₀ V U S H φ) :
    tSub16 V₀ S ⊓ centralizer (iSub16 V H : Set G) ≤ qSub16 V₀ V S H := by
  have c := e.cfg
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := (conjClosure V H ⊔ tSub16 V₀ S) ⊓ centralizer (iSub16 V H : Set G)
  have hTK : tSub16 V₀ S ≤ normalizer (conjClosure V H : Set G) :=
    (inf_le_left.trans c.min.fam16.1).trans (le_normalizer_conjClosure V H)
  haveI hKsubNorm : ((conjClosure V H).subgroupOf
      (tSub16 V₀ S ⊔ conjClosure V H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (sup_le hTK (le_normalizer (H := conjClosure V H)))
  have hC2 : IsPGroup 2 C := by
    have hT2 : IsPGroup 2 (tSub16 V₀ S) := c.cex.sylow.isPGroup.to_le inf_le_left
    let Ksub : Subgroup ↥(tSub16 V₀ S ⊔ conjClosure V H) :=
      (conjClosure V H).subgroupOf (tSub16 V₀ S ⊔ conjClosure V H)
    haveI : Ksub.Normal := hKsubNorm
    let X := ↥(tSub16 V₀ S ⊔ conjClosure V H) ⧸ Ksub
    have hX2 : IsPGroup 2 X :=
      CFSG.GroupTheory.isPGroup_quotient_sup_left (p := 2) (T := tSub16 V₀ S)
        (C := conjClosure V H) hT2
    have hCL : C ≤ tSub16 V₀ S ⊔ conjClosure V H :=
      inf_le_left.trans (le_of_eq (sup_comm (conjClosure V H) (tSub16 V₀ S)))
    let f : C →* X := (QuotientGroup.mk' Ksub).comp (Subgroup.inclusion hCL)
    have hI2 : IsPGroup 2 (iSub16 V H) :=
      B2F.isPGroup_of_isElemAbelian (Cex16.isElemAbelian_iSub16 c.one c.std c.cex c.min.fam16)
    have hIsub2 : IsPGroup 2 ((iSub16 V H).subgroupOf C) := hI2.comap_subtype
    have hker_le : f.ker ≤ (iSub16 V H).subgroupOf C := by
      intro d hd
      have hdK : (d : G) ∈ conjClosure V H := by
        have h1 : f d = 1 := MonoidHom.mem_ker.mp hd
        have h2 : (Subgroup.inclusion hCL d : X) = 1 := by
          show f d = 1
          exact h1
        have h3 : Subgroup.inclusion hCL d ∈ Ksub :=
          (QuotientGroup.eq_one_iff (Subgroup.inclusion hCL d)).mp h2
        simpa only [Ksub, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion] using h3
      have hdCI : (d : G) ∈ centralizer (iSub16 V H : Set G) := (Subgroup.mem_inf.mp d.2).2
      exact Subgroup.mem_subgroupOf.mpr (inf_centralizer_le_iSub16 e ⟨hdK, hdCI⟩)
    have htop2 : IsPGroup 2 (⊤ : Subgroup C) := by
      have h := IsPGroup.comap_of_ker_isPGroup (hX2.to_subgroup (⊤ : Subgroup X)) f
        (hIsub2.to_le hker_le)
      rwa [Subgroup.comap_top] at h
    exact htop2.of_equiv Subgroup.topEquiv
  have hLnormI : conjClosure V H ⊔ tSub16 V₀ S ≤ normalizer (iSub16 V H : Set G) :=
    c.sup_le_H.trans (le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H)
  have hLnormC : conjClosure V H ⊔ tSub16 V₀ S ≤
      normalizer (centralizer (iSub16 V H : Set G) : Set G) :=
    hLnormI.trans (w16q_normalizer_centralizer_le (iSub16 V H))
  have hnormC : conjClosure V H ⊔ tSub16 V₀ S ≤ normalizer (C : Set G) :=
    (le_inf (le_normalizer (H := conjClosure V H ⊔ tSub16 V₀ S)) hLnormC).trans
      (inf_normalizer_le_normalizer_inf (H := conjClosure V H ⊔ tSub16 V₀ S)
        (K := centralizer (iSub16 V H : Set G)))
  have hCQ : C ≤ qSub16 V₀ V S H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (show C ≤ conjClosure V H ⊔ tSub16 V₀ S from inf_le_left) hnormC hC2
  intro x hx
  exact hCQ ⟨Subgroup.mem_sup_right hx.1, hx.2⟩

end Exc1616

end CFSG.LocalAnalysis.WeakClosure81

end
