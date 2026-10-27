module

public import CFSG.RankThree.GF2n.Stroth78.Sec4Three
public import CFSG.RankThree.GF2n.Stroth78.Sec2Nineteen

import CFSG.RankThree.GF2n.Stroth78.Sec3Five
import CFSG.RankThree.GF2n.Stroth78.Sec2Six
import CFSG.GroupTheory.ThreeTranspositions.TransvectionSymplectic

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions
open CFSG.Blueprint.Fischer CFSG.Fischer.Classification
open scoped commutatorElement

namespace Sec4Five

theorem mul_comm_of_mul_self {V : Type*} [Group V] (h2 : ∀ u : V, u * u = 1) (a b : V) :
    a * b = b * a := by
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_left (h2 a)
  have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_left (h2 b)
  have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_left (h2 (a * b))
  rw [← hab, mul_inv_rev, ha, hb]

theorem mulAut_commute_of_fix {V : Type*} [Group V] (h2 : ∀ u : V, u * u = 1)
    {t : MulAut V} {c : V} (hc : ∀ u, t u = u ∨ t u = u * c)
    {σ τ : MulAut V} (hσ : ∀ u, t u = u → σ u = u) (hτ : ∀ u, t u = u → τ u = u) :
    σ * τ = τ * σ := by
  have hcomm := mul_comm_of_mul_self h2
  have hδ : ∀ {π : MulAut V}, (∀ u, t u = u → π u = u) → ∀ u, t (π u * u⁻¹) = π u * u⁻¹ := by
    intro π hπ u
    by_cases hu : t u = u
    · rw [hπ u hu, mul_inv_cancel, map_one]
    · have htu : t u = u * c := (hc u).resolve_left hu
      have hπu : t (π u) = π u * c := by
        refine (hc (π u)).resolve_left fun h => hu ?_
        have := hπ (π u) h
        rw [π.injective this] at h
        exact h
      rw [map_mul, map_inv, hπu, htu]
      group
  ext u
  have key : ∀ x : V, x = u * (x * u⁻¹) := fun x => by rw [hcomm u]; group
  change σ (τ u) = τ (σ u)
  have hτu := hσ _ (hδ hτ u)
  have hσu := hτ _ (hδ hσ u)
  calc σ (τ u) = σ (u * (τ u * u⁻¹)) := by rw [← key]
    _ = σ u * (τ u * u⁻¹) := by rw [map_mul, hτu]
    _ = u * (σ u * u⁻¹) * (τ u * u⁻¹) := by rw [← key]
    _ = u * (τ u * u⁻¹) * (σ u * u⁻¹) := by
          rw [mul_assoc u (σ u * u⁻¹), mul_assoc u (τ u * u⁻¹), hcomm (σ u * u⁻¹)]
    _ = τ u * (σ u * u⁻¹) := by rw [← key]
    _ = τ (u * (σ u * u⁻¹)) := by rw [map_mul, hσu]
    _ = τ (σ u) := by rw [← key]

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem eq_one_or_eq_of_mem_Rbar (S : Setting z E F) {a : G}
    (hR2 : Nat.card ↥(Rbar S a) = 2) {α : Hbar z} (hα : α ∈ Rbar S a) (hα1 : α ≠ 1)
    {r : Hbar z} (hr : r ∈ Rbar S a) : r = 1 ∨ r = α := by
  by_contra hne
  push Not at hne
  have hsub : ({1, α, r} : Set (Hbar z)) ⊆ (Rbar S a : Set (Hbar z)) := by
    rintro x (rfl | rfl | rfl)
    · exact (Rbar S a).one_mem
    · exact hα
    · exact hr
  have h3 : ({1, α, r} : Set (Hbar z)).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨1, α, r, hα1.symm, hne.1.symm, fun h => hne.2 h.symm, rfl⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h3, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hR2] at hle
  omega

theorem exists_conj_not_commute (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Rbar S a) (hα1 : α ≠ 1)
    (hna : NonabelianCommutator ↥(threeResidualQuot (alphaInX S h hα)))
    (hT : TripleProperty (threeResidualClass (alphaInX S h hα)))
    (hLS : IsSimpleGroup (commutator
      (LocalQuotient (threeResidualClass (alphaInX S h hα)) (alphaBar S h hα))))
    (hLna : ∃ x y : commutator
      (LocalQuotient (threeResidualClass (alphaInX S h hα)) (alphaBar S h hα)), x * y ≠ y * x)
    {x : ↥(threeResidualQuot (alphaInX S h hα))} (hxα : x * alphaBar S h hα = alphaBar S h hα * x)
    (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) (hxα' : x ≠ alphaBar S h hα) :
    ∃ g₁ ∈ CW (alphaInX S h hα), ∃ g₂ ∈ CW (alphaInX S h hα),
      residualProj (alphaInX S h hα) g₁ * x * (residualProj (alphaInX S h hα) g₁)⁻¹ *
          (residualProj (alphaInX S h hα) g₂ * x * (residualProj (alphaInX S h hα) g₂)⁻¹) ≠
        residualProj (alphaInX S h hα) g₂ * x * (residualProj (alphaInX S h hα) g₂)⁻¹ *
          (residualProj (alphaInX S h hα) g₁ * x * (residualProj (alphaInX S h hα) g₁)⁻¹) := by
  by_contra hall
  push Not at hall
  have hH := hyp_Wbar S h h217 h3 hα hα1
  have hπs : residualProj (alphaInX S h hα) (residualSelf (alphaInX S h hα)) =
      alphaBar S h hα := by
    apply Subtype.ext
    rw [residualProj_apply]
    rfl
  obtain ⟨K, hKdef⟩ : ∃ K : Set ↥(threeResidualQuot (alphaInX S h hα)),
      K = {y | ∃ g ∈ CW (alphaInX S h hα), y = residualProj (alphaInX S h hα) g * x *
        (residualProj (alphaInX S h hα) g)⁻¹} := ⟨_, rfl⟩
  have hKcomm : ∀ y ∈ K, ∀ y' ∈ K, y * y' = y' * y := by
    rw [hKdef]
    rintro _ ⟨g₁, hg₁, rfl⟩ _ ⟨g₂, hg₂, rfl⟩
    exact hall g₁ hg₁ g₂ hg₂
  have hKC : ∀ y ∈ K, y * alphaBar S h hα = alphaBar S h hα * y := by
    rw [hKdef]
    rintro _ ⟨g, hg, rfl⟩
    have hgs : g * residualSelf (alphaInX S h hα) = residualSelf (alphaInX S h hα) * g :=
      Subgroup.mem_centralizer_singleton_iff.mp hg
    have hgs' : Commute (residualProj (alphaInX S h hα) g) (alphaBar S h hα) := by
      have := congrArg (residualProj (alphaInX S h hα)) hgs
      rw [map_mul, map_mul, hπs] at this
      exact this
    exact ((hgs'.mul_left (show Commute x (alphaBar S h hα) from hxα)).mul_left
      hgs'.inv_left).eq
  obtain ⟨B, hBdef⟩ : ∃ B : Subgroup ↥(threeResidualQuot (alphaInX S h hα)),
      B = Subgroup.closure K := ⟨_, rfl⟩
  have hsq : ∀ y ∈ B, y ^ 2 = 1 ∧ ∀ y' ∈ K, y * y' = y' * y := by
    intro y hy
    rw [hBdef] at hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      refine ⟨?_, hKcomm y hy⟩
      rw [hKdef] at hy
      obtain ⟨g, -, rfl⟩ := hy
      rw [conj_pow, hx2, mul_one, mul_inv_cancel]
    | one => exact ⟨one_pow 2, fun y' _ => by rw [one_mul, mul_one]⟩
    | mul y y' hy hy' ihy ihy' =>
      have hyy' : y * y' = y' * y := by
        have hle : Subgroup.closure K ≤ Subgroup.centralizer {y} := by
          rw [Subgroup.closure_le]
          intro k hk
          exact Subgroup.mem_centralizer_singleton_iff.mpr (ihy.2 k hk).symm
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy')).symm
      refine ⟨by rw [Commute.mul_pow hyy' 2, ihy.1, ihy'.1, one_mul], fun k hk => ?_⟩
      rw [mul_assoc, ihy'.2 k hk, ← mul_assoc, ihy.2 k hk, mul_assoc]
    | inv y hy ihy =>
      refine ⟨by rw [inv_pow, ihy.1, inv_one], fun k hk => ?_⟩
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ihy.2 k hk, mul_assoc, mul_inv_cancel,
        mul_one]
  have hB2 : IsPGroup 2 B := fun b => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, (hsq b b.2).1]
    rfl)⟩
  have hBd : B ≤ Subgroup.centralizer {alphaBar S h hα} := by
    rw [hBdef, Subgroup.closure_le]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hKC y hy)
  have hMB : ∀ m ∈ localPerfectResidual (threeResidualClass (alphaInX S h hα))
      (alphaBar S h hα), ∀ b ∈ B, m * b * m⁻¹ ∈ B := by
    intro m hm b hb
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp (localPerfectResidual_le_map_J0W S h hα hm)
    have hjC : j ∈ CW (alphaInX S h hα) := by
      obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.mp hj
      exact c.2
    rw [hBdef] at hb ⊢
    induction hb using Subgroup.closure_induction with
    | mem y hy =>
      rw [hKdef] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      refine Subgroup.subset_closure (hKdef ▸ ⟨j * g, mul_mem hjC hg, ?_⟩)
      rw [map_mul]
      group
    | one =>
      rw [mul_one, mul_inv_cancel]
      exact one_mem _
    | mul y y' _ _ hy hy' =>
      have e : residualProj (alphaInX S h hα) j * (y * y') *
          (residualProj (alphaInX S h hα) j)⁻¹ =
        (residualProj (alphaInX S h hα) j * y * (residualProj (alphaInX S h hα) j)⁻¹) *
          (residualProj (alphaInX S h hα) j * y' * (residualProj (alphaInX S h hα) j)⁻¹) := by
        group
      rw [e]
      exact mul_mem hy hy'
    | inv y _ hy =>
      have e : residualProj (alphaInX S h hα) j * y⁻¹ * (residualProj (alphaInX S h hα) j)⁻¹ =
          (residualProj (alphaInX S h hα) j * y * (residualProj (alphaInX S h hα) j)⁻¹)⁻¹ := by
        group
      rw [e]
      exact inv_mem hy
  have hxB : x ∈ B := hBdef ▸ Subgroup.subset_closure (hKdef ▸ ⟨1, one_mem _, by
    rw [map_one]; group⟩)
  rcases eq_one_or_eq_of_isPGroup_normalized hH hna hT (alphaBar_mem S h hα) hLS hLna
    (localPerfectResidual_le_localGroup _ _)
    (fun c hc => centralizer_normalizes_localPerfectResidual hH hc)
    (commutator_le_map_localPerfectResidual hLS hLna) hB2 hBd hMB hxB with h1 | h1
  · exact hx1 h1
  · exact hxα' h1

theorem derivedSeries_two_le_ker_rhoW_of_mem_ker (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Rbar S a) (hα1 : α ≠ 1)
    {k : ↥(threeResidualJoin (alphaInX S h hα))}
    (hk : k ∈ (rhoW S a (alphaInX S h hα)).ker) (hk1 : residualProj (alphaInX S h hα) k ≠ 1) :
    derivedSeries ↥(threeResidualJoin (alphaInX S h hα)) 2 ≤
      (rhoW S a (alphaInX S h hα)).ker := by
  have hH := hyp_Wbar S h h217 h3 hα hα1
  have hNne : (rhoW S a (alphaInX S h hα)).ker.map (residualProj (alphaInX S h hα)) ≠ ⊥ := by
    intro hbot
    have hmem := Subgroup.mem_map_of_mem (residualProj (alphaInX S h hα)) hk
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hk1 hmem
  haveI : ((rhoW S a (alphaInX S h hα)).ker.map (residualProj (alphaInX S h hα))).Normal :=
    Subgroup.Normal.map (MonoidHom.normal_ker _) _ (residualProj_surjective _)
  have hNK' := commutator_le_of_normal hH.center hH.simple hNne
  have hG' := TransvectionSymplectic.commutator_le_sup_ker _ _ (residualProj_surjective _) hNK'
  exact TransvectionSymplectic.derivedSeries_two_le_ker _ _ (residualProj_ker_le_center _) hG'

theorem rhoZ_conj_apply_eq_self (S : Setting z E F) {a : G} {α : Hbar z}
    (hfix : ∀ l ∈ Lbar S a, ∀ v : ↥(ZQ z), rhoZ S α v = v → rhoZ S l v = v)
    {g : Hbar z} (hg : g * α = α * g) {l : Hbar z} (hl : l ∈ Lbar S a) {v : ↥(ZQ z)}
    (hv : rhoZ S α v = v) : rhoZ S (g * l * g⁻¹) v = v := by
  have hg' : α * g⁻¹ = g⁻¹ * α := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hg, ← mul_assoc, inv_mul_cancel, one_mul]
  have hw : rhoZ S α (rhoZ S g⁻¹ v) = rhoZ S g⁻¹ v := by
    rw [← MulAut.mul_apply, ← map_mul, hg', map_mul, MulAut.mul_apply, hv]
  rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hfix l hl _ hw, ← MulAut.mul_apply,
    ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

attribute [local instance] Xsub_normal

theorem derivedSeries_two_le_ker_rhoW_of_actL (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Rbar S a) (hα1 : α ≠ 1)
    (hna : NonabelianCommutator ↥(threeResidualQuot (alphaInX S h hα)))
    (hT : TripleProperty (threeResidualClass (alphaInX S h hα)))
    (hLS : IsSimpleGroup (commutator
      (LocalQuotient (threeResidualClass (alphaInX S h hα)) (alphaBar S h hα))))
    (hLna : ∃ x y : commutator
      (LocalQuotient (threeResidualClass (alphaInX S h hα)) (alphaBar S h hα)), x * y ≠ y * x)
    (l : ↥(Lbar S a)) {x : ↥(threeResidualQuot (alphaInX S h hα))}
    (hlx : actL S h hα l = MulAut.conj x) (hx1 : x ≠ 1) (hxα : x ≠ alphaBar S h hα) :
    derivedSeries ↥(threeResidualJoin (alphaInX S h hα)) 2 ≤
      (rhoW S a (alphaInX S h hα)).ker := by
  have hH := hyp_Wbar S h h217 h3 hα hα1
  by_cases hX : ∃ y ∈ Xsub S a, rhoZ S y ≠ 1
  swap
  · push Not at hX
    intro y _
    rw [MonoidHom.mem_ker]
    exact hX _ (y : ↥(Xsub S a)).2
  have hR := forall_Rbar_eq_one_of_rhoZ_Xsub S h h217 hX
  have hR2 : Nat.card ↥(Rbar S a) = 2 := card_Rbar_eq_two S h h217 h3
  have hfix : ∀ l ∈ Lbar S a, ∀ v : ↥(ZQ z), rhoZ S α v = v → rhoZ S l v = v := by
    intro l hl v hv
    refine rhoZ_Lbar_eq_self_of_forall_Rbar S h hR (fun r hr => ?_) hl
    rcases eq_one_or_eq_of_mem_Rbar S hR2 hα hα1 hr with rfl | rfl
    · rw [map_one]
      rfl
    · exact hv
  obtain ⟨c, hc⟩ := rhoZ_diff_eq_or S h hR2.le hα
  have hconjinj : Function.Injective
      (MulAut.conj : ↥(threeResidualQuot (alphaInX S h hα)) →* MulAut _) := by
    intro p q hpq
    have hc : q⁻¹ * p ∈ Subgroup.center ↥(threeResidualQuot (alphaInX S h hα)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hy := congrArg (fun φ : MulAut _ => φ y) hpq
      simp only [MulAut.conj_apply] at hy
      calc y * (q⁻¹ * p) = q⁻¹ * (q * y * q⁻¹) * p := by group
        _ = q⁻¹ * (p * y * p⁻¹) * p := by rw [hy]
        _ = q⁻¹ * p * y := by group
    rw [hH.center, Subgroup.mem_bot, inv_mul_eq_one] at hc
    exact hc.symm
  have hxC : x * alphaBar S h hα = alphaBar S h hα * x := by
    have hfx := actL_fix S h hα l
    rw [hlx, MulAut.conj_apply] at hfx
    have hfx' : x * alphaBar S h hα * x⁻¹ = alphaBar S h hα := hfx
    calc x * alphaBar S h hα = x * alphaBar S h hα * x⁻¹ * x := by group
      _ = alphaBar S h hα * x := by rw [hfx']
  have hx2 : x ^ 2 = 1 := by
    have hl2 : l * l = 1 := by
      apply Subtype.ext
      have := sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj l.2
      rw [sq] at this
      exact this
    have h2 := congrArg (actL S h hα) hl2
    rw [map_mul, map_one, hlx, ← map_mul] at h2
    rw [sq]
    exact hconjinj (h2.trans (map_one _).symm)
  obtain ⟨g₁, hg₁, g₂, hg₂, hne⟩ :=
    exists_conj_not_commute S h h217 h3 hα hα1 hna hT hLS hLna hxC hx2 hx1 hxα
  let cl : ↥(Subgroup.centralizer
      ({((alphaInX S h hα : ↥(Xsub S a)) : Hbar z)} : Set (Hbar z))) :=
    Subgroup.inclusion (Lbar_le_centralizer_alphaInX S h hα) l
  let ψ : ↥(threeResidualJoin (alphaInX S h hα)) ≃* ↥(threeResidualJoin (alphaInX S h hα)) :=
    ((MulAut.conjNormal (cl : Hbar z)).subgroupMap (threeResidualJoin (alphaInX S h hα))).trans
      (MulEquiv.subgroupCongr (map_conjNormal_threeResidualJoin cl))
  have hψι : ∀ y : ↥(threeResidualJoin (alphaInX S h hα)),
      (((ψ y : ↥(threeResidualJoin (alphaInX S h hα))) : ↥(Xsub S a)) : Hbar z) =
        (l : Hbar z) * ((y : ↥(Xsub S a)) : Hbar z) * (l : Hbar z)⁻¹ := by
    intro y
    change ((MulAut.conjNormal ((cl : Hbar z)) (y : ↥(Xsub S a)) : ↥(Xsub S a)) : Hbar z) = _
    rw [MulAut.conjNormal_apply]
    rfl
  have hψπ : ∀ y : ↥(threeResidualJoin (alphaInX S h hα)),
      residualProj (alphaInX S h hα) (ψ y) = x * residualProj (alphaInX S h hα) y * x⁻¹ := by
    intro y
    have hy := actL_apply S h hα l (y : ↥(Xsub S a)) (mk_mem_threeResidualQuot_of_mem y.2)
    rw [hlx, MulAut.conj_apply] at hy
    have hπy : residualProj (alphaInX S h hα) y = ⟨QuotientGroup.mk (y : ↥(Xsub S a)),
        mk_mem_threeResidualQuot_of_mem y.2⟩ :=
      Subtype.ext (residualProj_apply _ y)
    apply Subtype.ext
    rw [residualProj_apply, hπy, hy]
    rfl
  have hgα : ∀ g ∈ CW (alphaInX S h hα),
      ((g : ↥(Xsub S a)) : Hbar z) * α = α * ((g : ↥(Xsub S a)) : Hbar z) := by
    intro g hg
    have hgs : g * residualSelf (alphaInX S h hα) = residualSelf (alphaInX S h hα) * g :=
      Subgroup.mem_centralizer_singleton_iff.mp hg
    have := congrArg (fun y : ↥(threeResidualJoin (alphaInX S h hα)) =>
      ((y : ↥(Xsub S a)) : Hbar z)) hgs
    simpa using this
  obtain ⟨k, hk⟩ : ∃ k : ↥(threeResidualJoin (alphaInX S h hα)),
      k = (g₁ * ψ g₁⁻¹) * ψ ((g₂ * ψ g₂⁻¹) * (g₁ * ψ g₁⁻¹)⁻¹) * (g₂ * ψ g₂⁻¹)⁻¹ :=
    ⟨_, rfl⟩
  have hπk : residualProj (alphaInX S h hα) k =
      ⁅residualProj (alphaInX S h hα) g₁ * x * (residualProj (alphaInX S h hα) g₁)⁻¹,
        residualProj (alphaInX S h hα) g₂ * x * (residualProj (alphaInX S h hα) g₂)⁻¹⁆ := by
    rw [hk, commutatorElement_def]
    simp only [map_mul, map_inv, hψπ]
    group
  have hπk1 : residualProj (alphaInX S h hα) k ≠ 1 := by
    rw [hπk, Ne, commutatorElement_eq_one_iff_mul_comm]
    exact hne
  have hιk : ((k : ↥(Xsub S a)) : Hbar z) =
      ⁅((g₁ : ↥(Xsub S a)) : Hbar z) * (l : Hbar z) * ((g₁ : ↥(Xsub S a)) : Hbar z)⁻¹,
        ((g₂ : ↥(Xsub S a)) : Hbar z) * (l : Hbar z) * ((g₂ : ↥(Xsub S a)) : Hbar z)⁻¹⁆ := by
    rw [hk, commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hψι]
    group
  have hρk : rhoW S a (alphaInX S h hα) k = 1 := by
    change rhoZ S ((k : ↥(Xsub S a)) : Hbar z) = 1
    rw [hιk, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mulAut_commute_of_fix (ZQ_mul_self S) hc
      (fun v hv => rhoZ_conj_apply_eq_self S hfix (hgα g₁ hg₁) l.2 hv)
      (fun v hv => rhoZ_conj_apply_eq_self S hfix (hgα g₂ hg₂) l.2 hv)
  exact derivedSeries_two_le_ker_rhoW_of_mem_ker S h h217 h3 hα hα1
    (MonoidHom.mem_ker.mpr hρk) hπk1

end Sec4Five

end CFSG.RankThree.GF2n.Stroth78
