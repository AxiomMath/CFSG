module

public import CFSG.RankThree.OrthogonalInvolutions.Basic
import CFSG.RankThree.GF2n.Stroth80.Sec112Moved
import CFSG.RankThree.GF2n.Stroth80.Sec112Class
import CFSG.RankThree.GF2n.Stroth80.Sec112Model
import CFSG.RankThree.GF2n.Stroth80.Sec123Order
import CFSG.RankThree.OrthogonalInvolutions.A2Pairs
public import CFSG.RankThree.GF2n.Stroth80.Sec111Order
public import CFSG.RankThree.GF2n.Stroth80.Sec11Ebar

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.OrthogonalInvolutions (commSpace finrank_commSpace_inf_eq_one_of_commute
  commSpace_inf_eq_bot_of_odd_orderOf_mul le_sup_of_finrank_inf_eq_one)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

private theorem Ctx.finrank_commSpace_inf_eq_one [(Q.subgroupOf M).Normal] [CharP K 2]
    (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφiso : ∀ (g : ↥(H0 M Z)) (e : M₀.E), M₀.Qf (φ g e) = M₀.Qf e) {u f : Mbar M Q}
    (hu : u ∈ Ebar M Q Z B) (hf : f ∈ Ebar M Q Z B)
    (huf : ∀ x ∈ Xbar M Q Z B, x * u * x⁻¹ ≠ f) :
    Module.finrank K ↥(commSpace (liftF φ f) ⊓ commSpace (liftF φ u)) = 1 := by
  have hD := isRootInvolutionSet_A2Set_inter hc h hφπ hφker hφiso
  have huH := mem_bar_H0_iff.mp (hc.Ebar_subset_H hu)
  have hfH := mem_bar_H0_iff.mp (hc.Ebar_subset_H hf)
  have hcomm : Commute (liftF φ u) (liftF φ f) := by
    have e1 := liftF_mul hφker huH hfH
    have e2 := liftF_mul hφker hfH huH
    rw [hc.commute_of_not_conj hD hu hf huf] at e1
    exact e1.symm.trans e2
  rw [inf_comm]
  exact finrank_commSpace_inf_eq_one_of_commute
    (hc.isOrthA2_liftF_of_mem_Ebar h hφπ hφker hf).mul_self
    (hc.isOrthA2_liftF_of_mem_Ebar h hφπ hφker hu).finrank_eq hcomm
    (hc.exists_moved_of_not_conj hw hn h hφπ hφker hφiso hu hf huf)

theorem Ctx.commSpace_le_sup_of_not_conj [(Q.subgroupOf M).Normal] [CharP K 2]
    (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφiso : ∀ (g : ↥(H0 M Z)) (e : M₀.E), M₀.Qf (φ g e) = M₀.Qf e) {t f y : Mbar M Q}
    (ht : t ∈ Ebar M Q Z B) (hf : f ∈ Ebar M Q Z B)
    (hft : ∀ x ∈ Xbar M Q Z B, x * t * x⁻¹ ≠ f) (hy : y ∈ Xbar M Q Z B)
    (hodd : Odd (orderOf (t * (y * t * y⁻¹)))) (hne : t * (y * t * y⁻¹) ≠ 1) :
    commSpace (liftF φ f) ≤ commSpace (liftF φ t) ⊔ commSpace (liftF φ (y * t * y⁻¹)) := by
  have hs : y * t * y⁻¹ ∈ Ebar M Q Z B := hc.Ebar_conj ht y
  have hfs : ∀ x ∈ Xbar M Q Z B, x * (y * t * y⁻¹) * x⁻¹ ≠ f := by
    intro x hx hxf
    refine hft (x * y) ((Xbar M Q Z B).mul_mem hx hy) ?_
    rw [← hxf]
    group
  have htH := hc.Ebar_subset_H ht
  have htsH : t * (y * t * y⁻¹) ∈ bar M Q (H0 M Z) :=
    (bar M Q (H0 M Z)).mul_mem htH (hc.Ebar_subset_H hs)
  have hmul : liftF φ t * liftF φ (y * t * y⁻¹) = liftF φ (t * (y * t * y⁻¹)) :=
    (liftF_mul hφker (mem_bar_H0_iff.mp htH) (mem_bar_H0_iff.mp (hc.Ebar_subset_H hs))).symm
  have hodd' : Odd (orderOf (liftF φ t * liftF φ (y * t * y⁻¹))) := by
    rw [hmul, orderOf_liftF hφker htsH]
    exact hodd
  have hne' : liftF φ t * liftF φ (y * t * y⁻¹) ≠ 1 := by
    rw [hmul, Ne, ← orderOf_eq_one_iff, orderOf_liftF hφker htsH, orderOf_eq_one_iff]
    exact hne
  have hbot := (commSpace_inf_eq_bot_of_odd_orderOf_mul
    (polarBilin_toQuadraticForm_nondegenerate M₀)
    (hc.isOrthA2_liftF_of_mem_Ebar h hφπ hφker ht)
    (hc.isOrthA2_liftF_of_mem_Ebar h hφπ hφker hs) hodd' hne').1
  exact le_sup_of_finrank_inf_eq_one (hc.isOrthA2_liftF_of_mem_Ebar h hφπ hφker hf).finrank_eq
    (hc.finrank_commSpace_inf_eq_one hw hn h hφπ hφker hφiso ht hf hft)
    (hc.finrank_commSpace_inf_eq_one hw hn h hφπ hφker hφiso hs hf hfs) hbot

private theorem Ctx.plane_inf_eq_bot_of_odd_orderOf_mul_lift [(Q.subgroupOf M).Normal]
    [CharP K 2] (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    {u v : Mbar M Q}
    (hu : u ∈ Ebar M Q Z B) (hv : v ∈ Ebar M Q Z B)
    (hodd : Odd (orderOf (u * v))) (hne : u * v ≠ 1) :
    commSpace (liftF φ u) ⊓ commSpace (liftF φ v) = ⊥ ∧
      ∀ x ∈ commSpace (liftF φ u) ⊔ commSpace (liftF φ v),
        (∀ y ∈ commSpace (liftF φ u) ⊔ commSpace (liftF φ v),
          QuadraticMap.polar M₀.toQuadraticForm x y = 0) → x = 0 := by
  have huH := hc.Ebar_subset_H hu
  have hvH := hc.Ebar_subset_H hv
  have hmul : liftF φ u * liftF φ v = liftF φ (u * v) :=
    (liftF_mul hφker (mem_bar_H0_iff.mp huH) (mem_bar_H0_iff.mp hvH)).symm
  have hprod : u * v ∈ bar M Q (H0 M Z) := (bar M Q (H0 M Z)).mul_mem huH hvH
  have hodd' : Odd (orderOf (liftF φ u * liftF φ v)) := by
    rw [hmul, orderOf_liftF hφker hprod]
    exact hodd
  have hne' : liftF φ u * liftF φ v ≠ 1 := by
    rw [hmul, Ne, ← orderOf_eq_one_iff, orderOf_liftF hφker hprod, orderOf_eq_one_iff]
    exact hne
  exact commSpace_inf_eq_bot_of_odd_orderOf_mul (polarBilin_toQuadraticForm_nondegenerate M₀)
    (hc.isOrthA2_liftF_of_mem_Ebar h hφπ hφker hu)
    (hc.isOrthA2_liftF_of_mem_Ebar h hφπ hφker hv) hodd' hne'

private theorem Ctx.finrank_sup_plane_eq_four [(Q.subgroupOf M).Normal] [CharP K 2]
    (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    {u v : Mbar M Q}
    (hu : u ∈ Ebar M Q Z B) (hv : v ∈ Ebar M Q Z B)
    (hodd : Odd (orderOf (u * v))) (hne : u * v ≠ 1) :
    Module.finrank K ↥(commSpace (liftF φ u) ⊔ commSpace (liftF φ v)) = 4 := by
  have hbot := (hc.plane_inf_eq_bot_of_odd_orderOf_mul_lift h hφπ hφker hu hv hodd hne).1
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (commSpace (liftF φ u)) (commSpace (liftF φ v))
  rw [hbot, finrank_bot,
    (hc.isOrthA2_liftF_of_mem_Ebar h hφπ hφker hu).finrank_eq,
    (hc.isOrthA2_liftF_of_mem_Ebar h hφπ hφker hv).finrank_eq] at hdim
  omega

private theorem Ctx.sup_plane_eq_of_odd_partners [(Q.subgroupOf M).Normal] [CharP K 2]
    (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (h : GlobalModelData M Q Z γ M₀) {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφiso : ∀ (g : ↥(H0 M Z)) (e : M₀.E), M₀.Qf (φ g e) = M₀.Qf e) {t f y y' : Mbar M Q}
    (ht : t ∈ Ebar M Q Z B) (hf : f ∈ Ebar M Q Z B)
    (hft : ∀ x ∈ Xbar M Q Z B, x * t * x⁻¹ ≠ f)
    (hy : y ∈ Xbar M Q Z B) (hodd : Odd (orderOf (t * (y * t * y⁻¹))))
    (hne : t * (y * t * y⁻¹) ≠ 1)
    (hy' : y' ∈ Xbar M Q Z B) (hodd' : Odd (orderOf (f * (y' * f * y'⁻¹))))
    (hne' : f * (y' * f * y'⁻¹) ≠ 1) :
    commSpace (liftF φ f) ⊔ commSpace (liftF φ (y' * f * y'⁻¹)) =
      commSpace (liftF φ t) ⊔ commSpace (liftF φ (y * t * y⁻¹)) := by
  have hsE : y * t * y⁻¹ ∈ Ebar M Q Z B := hc.Ebar_conj ht y
  have hfE : y' * f * y'⁻¹ ∈ Ebar M Q Z B := hc.Ebar_conj hf y'
  have hft' : ∀ x ∈ Xbar M Q Z B, x * t * x⁻¹ ≠ y' * f * y'⁻¹ := by
    intro x hxX hxeq
    have hxy : (y'⁻¹ * x) * t * (y'⁻¹ * x)⁻¹ = f := by
      calc (y'⁻¹ * x) * t * (y'⁻¹ * x)⁻¹ = y'⁻¹ * (x * t * x⁻¹) * y' := by group
        _ = y'⁻¹ * (y' * f * y'⁻¹) * y' := by rw [hxeq]
        _ = f := by group
    exact hft (y'⁻¹ * x) ((Xbar M Q Z B).mul_mem ((Xbar M Q Z B).inv_mem hy') hxX) hxy
  have h1 := hc.commSpace_le_sup_of_not_conj hw hn h hφπ hφker hφiso ht hf hft hy hodd hne
  have h2 := hc.commSpace_le_sup_of_not_conj hw hn h hφπ hφker hφiso ht hfE hft' hy hodd hne
  have hle : commSpace (liftF φ f) ⊔ commSpace (liftF φ (y' * f * y'⁻¹)) ≤
      commSpace (liftF φ t) ⊔ commSpace (liftF φ (y * t * y⁻¹)) := sup_le h1 h2
  have hdim := hc.finrank_sup_plane_eq_four h hφπ hφker hf hfE hodd' hne'
  have hdimW := hc.finrank_sup_plane_eq_four h hφπ hφker ht hsE hodd hne
  exact Submodule.eq_of_le_of_finrank_eq hle (hdim.trans hdimW.symm)

private theorem Ctx.commSpace_le_sup_of_odd_partners [(Q.subgroupOf M).Normal] [CharP K 2]
    (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (h : GlobalModelData M Q Z γ M₀) {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφiso : ∀ (g : ↥(H0 M Z)) (e : M₀.E), M₀.Qf (φ g e) = M₀.Qf e) {t f y y' : Mbar M Q}
    (ht : t ∈ Ebar M Q Z B) (hf : f ∈ Ebar M Q Z B)
    (hft : ∀ x ∈ Xbar M Q Z B, x * t * x⁻¹ ≠ f)
    (hy : y ∈ Xbar M Q Z B) (hodd : Odd (orderOf (t * (y * t * y⁻¹))))
    (hne : t * (y * t * y⁻¹) ≠ 1)
    (hy' : y' ∈ Xbar M Q Z B) (hodd' : Odd (orderOf (f * (y' * f * y'⁻¹))))
    (hne' : f * (y' * f * y'⁻¹) ≠ 1) {e : Mbar M Q} (he : e ∈ Ebar M Q Z B) :
    commSpace (liftF φ e) ≤ commSpace (liftF φ t) ⊔ commSpace (liftF φ (y * t * y⁻¹)) := by
  by_cases hclass : ∃ x ∈ Xbar M Q Z B, x * t * x⁻¹ = e
  · obtain ⟨z, hz, hze⟩ := hclass
    have hfe : ∀ x ∈ Xbar M Q Z B, x * f * x⁻¹ ≠ e := by
      intro x hxX hxeq
      have h1 : (x⁻¹ * z) * t * (x⁻¹ * z)⁻¹ = f := by
        calc (x⁻¹ * z) * t * (x⁻¹ * z)⁻¹ = x⁻¹ * (z * t * z⁻¹) * x := by group
          _ = x⁻¹ * e * x := by rw [hze]
          _ = x⁻¹ * (x * f * x⁻¹) * x := by rw [← hxeq]
          _ = f := by group
      exact hft (x⁻¹ * z) ((Xbar M Q Z B).mul_mem ((Xbar M Q Z B).inv_mem hxX) hz) h1
    have hle := hc.commSpace_le_sup_of_not_conj hw hn h hφπ hφker hφiso hf he hfe hy' hodd' hne'
    rwa [hc.sup_plane_eq_of_odd_partners hw hn h hφπ hφker hφiso ht hf hft hy hodd hne hy' hodd'
      hne'] at hle
  · exact hc.commSpace_le_sup_of_not_conj hw hn h hφπ hφker hφiso ht he
      (fun x hxX hxeq => hclass ⟨x, hxX, hxeq⟩) hy hodd hne

omit [Finite K] in
private theorem Ctx.map_le_four_space [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) {f y' : Mbar M Q}
    (hf : f ∈ Ebar M Q Z B) {W : Submodule K M₀.E}
    (hW : W = commSpace (liftF φ f) ⊔ commSpace (liftF φ (y' * f * y'⁻¹)))
    (hE : ∀ e ∈ Ebar M Q Z B, commSpace (liftF φ e) ≤ W) (g : ↥(H0 M Z)) :
    W.map (φ g : M₀.E →ₗ[K] M₀.E) ≤ W := by
  have hcbar : mkH M Q Z g ∈ bar M Q (H0 M Z) := mem_bar_H0_iff.mpr ⟨g, rfl⟩
  have hstep : ∀ e ∈ Ebar M Q Z B,
      (commSpace (liftF φ e)).map (φ g : M₀.E →ₗ[K] M₀.E) ≤ W := by
    intro e he
    have hconj := commSpace_liftF_conj hφker hcbar (hc.Ebar_subset_H he)
    rw [liftF_mkH hφker g] at hconj
    rw [← hconj]
    exact hE _ (hc.Ebar_conj he _)
  rw [hW] at hstep ⊢
  rw [Submodule.map_sup]
  exact sup_le (hstep f hf) (hstep _ (hc.Ebar_conj hf y'))

theorem Ctx.exists_four_space_of_not_conj [(Q.subgroupOf M).Normal] [CharP K 2]
    (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφiso : ∀ (g : ↥(H0 M Z)) (e : M₀.E), M₀.Qf (φ g e) = M₀.Qf e) {t f : Mbar M Q}
    (ht : t ∈ Ebar M Q Z B) (hf : f ∈ Ebar M Q Z B)
    (hft : ∀ x ∈ Xbar M Q Z B, x * t * x⁻¹ ≠ f) :
    ∃ W : Submodule K M₀.E, Module.finrank K W = 4 ∧
      (∀ x ∈ W, (∀ y ∈ W, M₀.B x y = 0) → x = 0) ∧
      (∀ e ∈ Ebar M Q Z B, commSpace (liftF φ e) ≤ W) ∧
      ∀ g : ↥(H0 M Z), ∀ w ∈ W, φ g w ∈ W := by
  classical
  have hD := isRootInvolutionSet_A2Set_inter hc h hφπ hφker hφiso
  obtain ⟨y, hy, hodd, hne⟩ := hc.exists_odd_partner_Ebar hD ht
  obtain ⟨y', hy', hodd', hne'⟩ := hc.exists_odd_partner_Ebar hD hf
  have hs : y * t * y⁻¹ ∈ Ebar M Q Z B := hc.Ebar_conj ht y
  have hnd := hc.plane_inf_eq_bot_of_odd_orderOf_mul_lift h hφπ hφker ht hs hodd hne
  have hfin := hc.finrank_sup_plane_eq_four h hφπ hφker ht hs hodd hne
  have hspan := hc.sup_plane_eq_of_odd_partners hw hn h hφπ hφker hφiso ht hf hft hy hodd hne
    hy' hodd' hne'
  have hAll : ∀ e ∈ Ebar M Q Z B,
      commSpace (liftF φ e) ≤ commSpace (liftF φ t) ⊔ commSpace (liftF φ (y * t * y⁻¹)) :=
    fun e he => hc.commSpace_le_sup_of_odd_partners hw hn h hφπ hφker hφiso ht hf hft hy hodd
      hne hy' hodd' hne' he
  refine ⟨commSpace (liftF φ t) ⊔ commSpace (liftF φ (y * t * y⁻¹)), hfin, ?_, hAll, ?_⟩
  · intro x hx hxorth
    exact hnd.2 x hx fun z hz => by
      rw [Tim79.QuadModel.polar_toQuadraticForm]
      exact hxorth z hz
  · intro g w hw
    have hmap := hc.map_le_four_space hφker hf hspan.symm hAll g
    exact hmap (Submodule.mem_map_of_mem (f := (φ g : M₀.E →ₗ[K] M₀.E)) hw)

end CFSG.RankThree.GF2n.Stroth80
