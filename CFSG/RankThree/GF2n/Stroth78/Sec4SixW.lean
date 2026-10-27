module

public import CFSG.RankThree.GF2n.Stroth78.Sec4FiveBase
public import CFSG.RankThree.GF2n.Stroth78.Sec4Three

import CFSG.GroupTheory.ThreeTranspositions.TransvectionSpRigid
import CFSG.Fischer.Classification.Orthogonal2.SpRigid
import CFSG.RankThree.GF2n.Stroth78.Sec4Bound
import CFSG.RankThree.GF2n.Stroth78.Sec3Five
import CFSG.RankThree.GF2n.Stroth78.Sec4Two
import CFSG.RankThree.GF2n.Stroth78.Sec4FiveStepA
import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions
open CFSG.Blueprint.Fischer CFSG.Fischer.Classification Matrix
open CFSG.GroupTheory.ThreeTranspositions.TransvectionSpRigid

namespace Sec4SixW

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

attribute [local instance] Xsub_normal

theorem false_of_forall_Rbar_of_base (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α₀ : Hbar z} (hα₀ : α₀ ∈ Rbar S a) (hα₀1 : α₀ ≠ 1) {m : ℕ} (hm : 3 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hO₀ : fischerLinearModel (threeResidualClass (alphaInX S h hα₀))
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0))
    (hR : ∀ r ∈ Rbar S a, (∀ u : ↥(ZQ z), rhoZ S r u = u) → r = 1) : False := by
  classical
  have hR2 : Nat.card ↥(Rbar S a) = 2 := card_Rbar_eq_two S h h217 h3
  have hH := hyp_Wbar S h h217 h3 hα₀ hα₀1
  obtain ⟨Φ, hΦ⟩ := Orth2.exists_mulEquiv_isometryGroup_of_fischerLinearModel halt hO₀
  have hperf := Orth2.commutator_eq_top_of_mulEquiv_isometryGroup hm halt hnd Φ
  have himg := image_residualProj_residualClassW (alphaInX S h hα₀)
  have hker := residualProj_ker_le_center (alphaInX S h hα₀)
  have hodd := odd_card_ker_residualProj (alphaInX S h hα₀) (odd_card_center_Xsub S a)
  have hπ := residualProj_surjective (alphaInX S h hα₀)
  have hrs2 : residualSelf (alphaInX S h hα₀) * residualSelf (alphaInX S h hα₀) = 1 := by
    rw [← sq]; exact residualSelf_alphaInX_sq S h hα₀
  have hself : ∀ x ∈ residualClassW (alphaInX S h hα₀), x * x = 1 := by
    rintro _ ⟨g, rfl⟩
    calc g * residualSelf (alphaInX S h hα₀) * g⁻¹ * (g * residualSelf (alphaInX S h hα₀) * g⁻¹)
        = g * (residualSelf (alphaInX S h hα₀) * residualSelf (alphaInX S h hα₀)) * g⁻¹ := by
          group
      _ = 1 := by rw [hrs2, mul_one, mul_inv_cancel]
  have hD3 : ∀ x ∈ residualClassW (alphaInX S h hα₀), ∀ y ∈ residualClassW (alphaInX S h hα₀),
      orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ) := by
    intro x hx y hy
    have hxE := residualClassW_coe_mem_Eset S h hα₀ hα₀1 hx
    have hyE := residualClassW_coe_mem_Eset S h hα₀ hα₀1 hy
    have hle := h3 _ hxE _ hyE
    have hco : orderOf (((x : ↥(Xsub S a)) : Hbar z) * ((y : ↥(Xsub S a)) : Hbar z)) =
        orderOf (x * y) := by
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    rw [hco] at hle
    have hpos : 0 < orderOf (x * y) := orderOf_pos _
    have : orderOf (x * y) = 1 ∨ orderOf (x * y) = 2 ∨ orderOf (x * y) = 3 := by omega
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  have hrsD : residualSelf (alphaInX S h hα₀) ∈ residualClassW (alphaInX S h hα₀) :=
    ⟨1, by group⟩
  obtain ⟨c₀, hc₀⟩ := rhoZ_diff_eq_or S h hR2.le hα₀
  have hρrs : rhoW S a (alphaInX S h hα₀) (residualSelf (alphaInX S h hα₀)) = rhoZ S α₀ := rfl
  have htv : ∀ e ∈ residualClassW (alphaInX S h hα₀), ∃ c : ↥(ZQ z), ∀ u,
      rhoW S a (alphaInX S h hα₀) e u = u ∨ rhoW S a (alphaInX S h hα₀) e u = u * c := by
    rintro _ ⟨g, rfl⟩
    refine ⟨rhoW S a (alphaInX S h hα₀) g c₀, ?_⟩
    rw [map_mul, map_mul, map_inv, hρrs]
    exact tv_conj hc₀
  choose! C hC using htv
  have hne1 : ∀ e ∈ residualClassW (alphaInX S h hα₀), rhoW S a (alphaInX S h hα₀) e ≠ 1 := by
    rintro _ ⟨g, rfl⟩ h1
    rw [map_mul, map_mul, map_inv, hρrs] at h1
    have : rhoZ S α₀ = 1 := by
      have := congrArg (fun φ => (rhoW S a (alphaInX S h hα₀) g)⁻¹ * φ *
        rhoW S a (alphaInX S h hα₀) g) h1
      simpa [mul_assoc] using this
    exact hα₀1 (hR α₀ hα₀ fun u => by rw [this]; rfl)
  have hK : Hyp ↥(threeResidualQuot (alphaInX S h hα₀))
      (residualProj (alphaInX S h hα₀) '' residualClassW (alphaInX S h hα₀)) := by
    rw [himg]; exact hH
  have hinj := injOn_of_commutator_eq_top (rhoW S a (alphaInX S h hα₀))
    (residualProj (alphaInX S h hα₀)) hπ hker hodd hself hK hperf hrsD (hne1 _ hrsD)
  have hsep := exists_separating_of_model hker hodd hself hD3 halt hnd Φ
    (by rw [himg]; exact hΦ)
  have hCinj := center_injOn (ZQ_mul_self S) (rhoW S a (alphaInX S h hα₀)) hself hD3 C hC
    hne1 hinj hsep
  have hπs : residualProj (alphaInX S h hα₀) (residualSelf (alphaInX S h hα₀)) =
      alphaBar S h hα₀ := by
    apply Subtype.ext
    rw [residualProj_apply]
    rfl
  have hact : ∀ l : ↥(Lbar S a),
      actL S h hα₀ l = 1 ∨ actL S h hα₀ l = MulAut.conj (alphaBar S h hα₀) := by
    intro l
    let cl : ↥(Subgroup.centralizer
        ({((alphaInX S h hα₀ : ↥(Xsub S a)) : Hbar z)} : Set (Hbar z))) :=
      Subgroup.inclusion (Lbar_le_centralizer_alphaInX S h hα₀) l
    let ψ : ↥(threeResidualJoin (alphaInX S h hα₀)) ≃*
        ↥(threeResidualJoin (alphaInX S h hα₀)) :=
      ((MulAut.conjNormal (cl : Hbar z)).subgroupMap
        (threeResidualJoin (alphaInX S h hα₀))).trans
        (MulEquiv.subgroupCongr (map_conjNormal_threeResidualJoin cl))
    have hψι : ∀ y : ↥(threeResidualJoin (alphaInX S h hα₀)),
        (((ψ y : ↥(threeResidualJoin (alphaInX S h hα₀))) : ↥(Xsub S a)) : Hbar z) =
          (l : Hbar z) * ((y : ↥(Xsub S a)) : Hbar z) * (l : Hbar z)⁻¹ := by
      intro y
      change ((MulAut.conjNormal ((cl : Hbar z)) (y : ↥(Xsub S a)) : ↥(Xsub S a)) : Hbar z) = _
      rw [MulAut.conjNormal_apply]
      rfl
    have hlα : (l : Hbar z) * α₀ = α₀ * (l : Hbar z) :=
      (Subgroup.mem_centralizer_iff.mp (Lbar_le_centralizer_alphaInX S h hα₀ l.2) α₀
        (Set.mem_singleton _)).symm
    have hψrs : ψ (residualSelf (alphaInX S h hα₀)) = residualSelf (alphaInX S h hα₀) := by
      apply Subtype.ext; apply Subtype.ext
      rw [hψι]
      change (l : Hbar z) * α₀ * (l : Hbar z)⁻¹ = α₀
      rw [hlα, mul_inv_cancel_right]
    have hψD : ∀ e ∈ residualClassW (alphaInX S h hα₀),
        ψ e ∈ residualClassW (alphaInX S h hα₀) := by
      rintro _ ⟨g, rfl⟩
      refine ⟨ψ g, ?_⟩
      rw [map_mul, map_mul, map_inv, hψrs]
    have hκ : ∀ e ∈ residualClassW (alphaInX S h hα₀),
        rhoW S a (alphaInX S h hα₀) (ψ e) =
          rhoZ S (l : Hbar z) * rhoW S a (alphaInX S h hα₀) e * (rhoZ S (l : Hbar z))⁻¹ := by
      intro e _
      change rhoZ S (((ψ e : ↥(threeResidualJoin (alphaInX S h hα₀))) : ↥(Xsub S a)) :
        Hbar z) = _
      rw [hψι, map_mul, map_mul, map_inv]
      rfl
    have hσ : ∀ u, rhoW S a (alphaInX S h hα₀) (residualSelf (alphaInX S h hα₀)) u = u →
        rhoZ S (l : Hbar z) u = u := by
      intro u hu
      refine rhoZ_Lbar_eq_self_of_forall_Rbar S h hR (fun r hr => ?_) l.2
      rcases Sec4Five.eq_one_or_eq_of_mem_Rbar S hR2 hα₀ hα₀1 hr with rfl | rfl
      · rw [map_one]; rfl
      · exact hu
    have hfixW := eq_self_of_equivariant (ZQ_mul_self S) (rhoW S a (alphaInX S h hα₀)) C hC
      hne1 hCinj (rhoZ S (l : Hbar z)) ψ hψD hκ hrsD hσ
    have hψπ : ∀ y : ↥(threeResidualJoin (alphaInX S h hα₀)),
        actL S h hα₀ l (residualProj (alphaInX S h hα₀) y) =
          residualProj (alphaInX S h hα₀) (ψ y) := by
      intro y
      have hy := actL_apply S h hα₀ l (y : ↥(Xsub S a)) (mk_mem_threeResidualQuot_of_mem y.2)
      have hπy : residualProj (alphaInX S h hα₀) y =
          ⟨QuotientGroup.mk (y : ↥(Xsub S a)), mk_mem_threeResidualQuot_of_mem y.2⟩ :=
        Subtype.ext (residualProj_apply _ y)
      rw [hπy]
      apply Subtype.ext
      rw [hy, residualProj_apply]
      rfl
    refine Orth2.eq_one_or_eq_conj_of_fix_commute hH.pair.2.2.2.2 halt hnd Φ hΦ
      (alphaBar_mem S h hα₀) (actL S h hα₀ l)
      (fun x hx => actL_mem_threeResidualClass S h hα₀ l hx) fun x hx hxα => ?_
    rw [← himg] at hx
    obtain ⟨e, he, rfl⟩ := hx
    rw [← hπs] at hxα
    have hed : e * residualSelf (alphaInX S h hα₀) = residualSelf (alphaInX S h hα₀) * e := by
      exact commute_of_pi_commute hker hodd hself hD3 he hrsD hxα
    rw [hψπ, hfixW e he hed]
  have hsub : ((actL S h hα₀).range : Set (MulAut _)) ⊆
      ({1, MulAut.conj (alphaBar S h hα₀)} : Set (MulAut _)) := by
    rintro _ ⟨l, rfl⟩
    rcases hact l with h1 | h1
    · left; exact h1
    · right; exact h1
  have h1 : Nat.card ((actL S h hα₀).range : Set (MulAut _)) ≤
      Nat.card ({1, MulAut.conj (alphaBar S h hα₀)} : Set (MulAut _)) :=
    Nat.card_mono (Set.toFinite _) hsub
  have h2 : Nat.card ({1, MulAut.conj (alphaBar S h hα₀)} : Set (MulAut _)) ≤ 2 := by
    rw [Nat.card_coe_set_eq]
    calc ({1, MulAut.conj (alphaBar S h hα₀)} : Set (MulAut _)).ncard
        ≤ ({MulAut.conj (alphaBar S h hα₀)} : Set (MulAut _)).ncard + 1 :=
          Set.ncard_insert_le _ _
      _ = 1 + 1 := by rw [Set.ncard_singleton]
      _ = 2 := rfl
  have h3' : Nat.card (actL S h hα₀).range ≤ 2 := le_trans (le_of_eq rfl) (h1.trans h2)
  have h4 := card_Lbar_le_two_mul_card_range_actL S h h217 h3 hα₀ hα₀1
  exact false_of_card_Lbar_le_four S h (by omega)

theorem rhoZ_Xsub_eq_one (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a) {m : ℕ} (hm : 3 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hsp : fischerLinearModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) :
    ∀ x ∈ Xsub S a, rhoZ S x = 1 := by
  by_contra hX
  push Not at hX
  have hR := forall_Rbar_eq_one_of_rhoZ_Xsub S h h217 hX
  obtain ⟨α₀, hα₀, hα₀1, hO₀⟩ :=
    Sec4Five.exists_mem_Rbar_fischerLinearModel S h h217 h3 hα hsp
  exact false_of_forall_Rbar_of_base S h h217 h3 hα₀ hα₀1 hm halt hnd hO₀ hR

theorem commute_of_mem_Xsub (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a) {m : ℕ} (hm : 3 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hsp : fischerLinearModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0))
    (x : ↥(H z)) (hx : (QuotientGroup.mk x : Hbar z) ∈ Xsub S a) {v : G} (hv : v ∈ ZQ z) :
    Commute (x : G) v := by
  have h1 := rhoZ_Xsub_eq_one S h h217 h3 hα hm halt hnd hsp _ hx
  have h2 := rhoZ_mk S x ⟨v, hv⟩
  rw [h1, MulAut.one_apply] at h2
  have h3' : (x : G) * v * (x : G)⁻¹ = v := h2.symm
  calc (x : G) * v = (x : G) * v * (x : G)⁻¹ * (x : G) := by group
    _ = v * (x : G) := by rw [h3']

end Sec4SixW

end CFSG.RankThree.GF2n.Stroth78
