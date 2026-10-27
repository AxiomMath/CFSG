module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEnd

import CFSG.GH74.Exceptional.UnitaryFourTwo
import CFSG.GroupTheory.PerfectSmallModuleSeven
import CFSG.Quasithin.Vol2.GoldschmidtKGHatA6F4
import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEndCent
import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEndPlane
import CFSG.RankThree.GF2n.Stroth78.Sec4Two

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions
open CFSG.Blueprint.Fischer CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
open Matrix Module

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

attribute [local instance] Xsub_normal

namespace Sec4PSUEnd

private theorem rhoLin_one_aux (S : Setting z E F) : rhoLin S 1 = 1 := by simp [rhoLin]

@[expose] noncomputable def rhoLinRestrict (S : Setting z E F) (K : Subgroup (Hbar z))
    (U : Submodule (ZMod 2) (Additive (QbarOf S)))
    (hU : ∀ x ∈ K, ∀ u ∈ U, rhoLin S x u ∈ U) : ↥K →* (↥U ≃ₗ[ZMod 2] ↥U) where
  toFun x := LinearEquiv.ofLinear
    ((rhoLin S x : _ →ₗ[ZMod 2] _).restrict (hU x x.2))
    ((rhoLin S (x : Hbar z)⁻¹ : _ →ₗ[ZMod 2] _).restrict (hU _ (inv_mem x.2)))
    (LinearMap.ext fun u => Subtype.ext <| by
      show rhoLin S x (rhoLin S (x : Hbar z)⁻¹ u) = u
      rw [← LinearEquiv.mul_apply, ← rhoLin_mul, mul_inv_cancel, rhoLin_one_aux]
      rfl)
    (LinearMap.ext fun u => Subtype.ext <| by
      show rhoLin S (x : Hbar z)⁻¹ (rhoLin S x u) = u
      rw [← LinearEquiv.mul_apply, ← rhoLin_mul, inv_mul_cancel, rhoLin_one_aux]
      rfl)
  map_one' := LinearEquiv.ext fun u => Subtype.ext <| by
    show rhoLin S 1 u = u
    rw [rhoLin_one_aux]
    rfl
  map_mul' x y := LinearEquiv.ext fun u => Subtype.ext <| by
    show rhoLin S ((x : Hbar z) * y) u = rhoLin S x (rhoLin S y u)
    rw [rhoLin_mul, LinearEquiv.mul_apply]

private theorem card_eq_three_of_odd_of_dvd_six {Y : Type*} [Group Y] [Finite Y]
    {K : Subgroup Y} (hodd : Odd (Nat.card K)) (h6 : Nat.card K ∣ 6) {g : Y} (hg : g ∈ K)
    (hg1 : g ≠ 1) : Nat.card K = 3 ∧ orderOf g = 3 ∧ Subgroup.zpowers g = K := by
  have hdvd : orderOf g ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hg
  have hgo : orderOf g ≠ 1 := fun h1 => hg1 (orderOf_eq_one_iff.mp h1)
  obtain ⟨k, hk⟩ := hodd
  have hle : Nat.card K ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  have hK3 : Nat.card K = 3 := by
    have h135 : Nat.card K = 1 ∨ Nat.card K = 3 ∨ Nat.card K = 5 := by omega
    rcases h135 with h1 | h3 | h5
    · rw [h1, Nat.dvd_one] at hdvd
      exact absurd hdvd hgo
    · exact h3
    · rw [h5] at h6
      norm_num at h6
  have hg3 : orderOf g = 3 := by
    rw [hK3] at hdvd
    exact ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left hgo
  refine ⟨hK3, hg3, Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hg) ?_⟩
  rw [Nat.card_zpowers, hg3, hK3]

private theorem facts_of_aVec_add (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {ρ : Hbar z} (hρ3 : ρ ^ 3 = 1)
    (hsum : aVec S h.mem_Q + rhoLin S ρ (aVec S h.mem_Q) + rhoLin S (ρ * ρ) (aVec S h.mem_Q) = 0) :
    rhoLin S ρ (aVec S h.mem_Q) ≠ aVec S h.mem_Q ∧ aVec S h.mem_Q ∈ commSpace (rhoLin S ρ) ∧
      ∀ u ∈ commSpace (rhoLin S ρ), rhoLin S ρ (rhoLin S ρ u) = rhoLin S ρ u + u := by
  have hp0 : aVec S h.mem_Q ≠ 0 := aV_ne_zero S h.mem_Q h.not_mem_ZQ
  refine ⟨fun hfix => hp0 ?_, ?_, fun u hu => ?_⟩
  · have h2 : rhoLin S (ρ * ρ) (aVec S h.mem_Q) = aVec S h.mem_Q := by
      rw [rhoLin_mul, LinearEquiv.mul_apply, hfix, hfix]
    have hpp : aVec S h.mem_Q + aVec S h.mem_Q = 0 := by
      rw [← sub_eq_add_vec (ZMod 2), sub_self]
    rw [hfix, h2, hpp, zero_add] at hsum
    exact hsum
  · have hmem := sub_mem_commSpace (rhoLin S ρ) (rhoLin S ρ (aVec S h.mem_Q))
    have heq : rhoLin S ρ (rhoLin S ρ (aVec S h.mem_Q)) - rhoLin S ρ (aVec S h.mem_Q) =
        aVec S h.mem_Q := by
      rw [← LinearEquiv.mul_apply, ← rhoLin_mul, sub_eq_add_vec (ZMod 2), add_comm]
      rw [add_assoc] at hsum
      exact ((eq_neg_of_add_eq_zero_left hsum).trans (neg_vec_eq (ZMod 2) _)).symm
    rwa [heq] at hmem
  · obtain ⟨v, rfl⟩ := mem_commSpace.mp hu
    have hccc : rhoLin S ρ (rhoLin S ρ (rhoLin S ρ v)) = v := by
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← rhoLin_mul, ← rhoLin_mul,
        ← pow_three', hρ3, rhoLin_one_aux]
      rfl
    rw [map_sub, map_sub, hccc,
      show rhoLin S ρ (rhoLin S ρ v) - rhoLin S ρ v + (rhoLin S ρ v - v) =
        rhoLin S ρ (rhoLin S ρ v) - v by abel,
      sub_eq_add_vec (ZMod 2), sub_eq_add_vec (ZMod 2), add_comm]

private theorem isSimpleGroup_quotient_center_Xsub (S : Setting z E F) {a : G} {w : ℕ}
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
    {α : Hbar z} (hα : α ∈ Tset S a)
    (hpsu : fischerCentralQuotientModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4) fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0)) :
    IsSimpleGroup (↥(Xsub S a) ⧸ Subgroup.center ↥(Xsub S a)) := by
  obtain ⟨φ⟩ := nonempty_mulEquiv_U2 S h h217 h3 hα hpsu
  have : IsSimpleGroup CFSG.GH74.Exceptional.PSp43 :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod 3) 2 (by norm_num)
      (Or.inr (Or.inl ⟨by rw [Nat.card_eq_fintype_card, ZMod.card], le_rfl⟩))
  have : IsSimpleGroup (U2 4) := CFSG.GH74.Exceptional.psp43EquivU2.symm.isSimpleGroup
  exact φ.isSimpleGroup

theorem center_Xsub_eq_bot (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a)
    (hpsu : fischerCentralQuotientModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4) fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0))
    (hw : w ≤ 5) :
    Subgroup.center ↥(Xsub S a) = ⊥ := by
  classical
  by_contra hZ
  obtain ⟨⟨c₀, hc₀Z⟩, hc₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
  have hc1 : (c₀ : Hbar z) ≠ 1 := fun h1 => hc₀1 (Subtype.ext (Subtype.ext h1))
  obtain ⟨Zb, hZbdef⟩ : ∃ Zb : Subgroup (Hbar z),
      Zb = (Subgroup.center ↥(Xsub S a)).map (Xsub S a).subtype := ⟨_, rfl⟩
  have hZbn : Zb.Normal := by
    rw [hZbdef]
    infer_instance
  have hZbC : Zb ≤ Subgroup.centralizer (Xsub S a : Set (Hbar z)) := by
    rw [hZbdef]
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨x, hx⟩)
  have hcZb : (c₀ : Hbar z) ∈ Zb := by
    rw [hZbdef]
    exact ⟨c₀, hc₀Z, rfl⟩
  have hZbcard : Nat.card Zb = Nat.card (Subgroup.center ↥(Xsub S a)) := by
    rw [hZbdef]
    exact Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hZbodd : Odd (Nat.card Zb) := hZbcard ▸ odd_card_center_Xsub S a
  obtain ⟨hZb3, hc3, hcZbeq⟩ := card_eq_three_of_odd_of_dvd_six hZbodd
    ((Subgroup.card_dvd_of_le hZbC).trans (card_centralizer_Xsub_dvd_six S h h217)) hcZb hc1
  have hcpow : (c₀ : Hbar z) ^ 3 = 1 := hc3 ▸ pow_orderOf_eq_one _
  have hLc : Lbar S a ≤ Subgroup.normalizer (Subgroup.zpowers (c₀ : Hbar z) : Set (Hbar z)) := by
    rw [hcZbeq, Subgroup.normalizer_eq_top_iff.mpr hZbn]
    exact le_top
  obtain ⟨⟨α₀, hα₀R⟩, hα₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.Rbar_ne_bot
  have hα₀1' : α₀ ≠ 1 := fun h1 => hα₀1 (Subtype.ext h1)
  have hα₀X : α₀ ∈ Xsub S a :=
    subset_Xsub S a (Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hα₀R hα₀1'))
  have hcC := hZbC hcZb
  have hcα : (c₀ : Hbar z) * α₀ = α₀ * c₀ :=
    (Subgroup.mem_centralizer_iff.mp hcC α₀ hα₀X).symm
  have hsum := (aVec_add_rhoLin_add_rhoLin_eq_zero S h h217 hcpow hc1 hLc hα₀R hα₀1' hcα).1
  obtain ⟨hca, haU, hz3⟩ := facts_of_aVec_add S h hcpow hsum
  have : Finite (Additive (QbarOf S)) := inferInstance
  have : Module.Finite (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  have hdim := finrank_QbarOf_eq_two_mul S h.card_F
  obtain ⟨U, hUdef⟩ : ∃ U, U = commSpace (rhoLin S (c₀ : Hbar z)) := ⟨_, rfl⟩
  rw [← hUdef] at haU hz3
  have hUX : ∀ x ∈ Xsub S a, ∀ u ∈ U, rhoLin S x u ∈ U := fun x hx u hu => by
    rw [hUdef] at hu ⊢
    exact rhoLin_mem_commSpace_of_commute S (Subgroup.mem_centralizer_iff.mp hcC x hx) hu
  have hU6 : 6 ≤ finrank (ZMod 2) U := by
    by_contra hlt
    obtain ⟨x, hx, hxa⟩ := exists_rhoLin_aVec_ne S h h217 h3 hα hpsu
    exact hxa (rhoLin_eq_self_of_finrank_le_five S h h217 h3 hα hpsu hUX (by omega) x hx _ haU)
  have hU10 : finrank (ZMod 2) U ≤ 2 * w := hdim ▸ Submodule.finrank_le U
  have hcomm : ∀ γ : ↥(Xsub S a), (γ : Hbar z) * c₀ = c₀ * γ := fun γ =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hc₀Z γ)
  let act : ↥(Xsub S a) →* (↥U →ₗ[ZMod 2] ↥U) :=
    { toFun := fun x => (rhoLin S x : _ →ₗ[ZMod 2] _).restrict (hUX x x.2)
      map_one' := LinearMap.ext fun u => Subtype.ext <| by
        show rhoLin S 1 u = u
        rw [rhoLin_one_aux]
        rfl
      map_mul' := fun x y => LinearMap.ext fun u => Subtype.ext <| by
        show rhoLin S ((x : Hbar z) * y) u = rhoLin S x (rhoLin S y u)
        rw [rhoLin_mul, LinearEquiv.mul_apply] }
  have hz : ∀ u, act c₀ (act c₀ u) = act c₀ u + u := fun u => Subtype.ext (hz3 u.1 u.2)
  have hact : ∀ γ u, act γ (act c₀ u) = act c₀ (act γ u) := fun γ u => Subtype.ext <| by
    show rhoLin S γ (rhoLin S c₀ u) = rhoLin S c₀ (rhoLin S γ u)
    rw [← LinearEquiv.mul_apply, ← rhoLin_mul, hcomm γ, rhoLin_mul, LinearEquiv.mul_apply]
  have hΓ : Group.IsPerfect ↥(Xsub S a) :=
    Subgroup.isPerfect_iff.2 (commutator_Xsub S h h217 h3 hα hpsu)
  have h3dvd := CFSG.Quasithin.Vol2.KGHat.three_dvd_finrank (act c₀) hz hΓ act hact c₀
    (fun _ => rfl)
  have hcard4 := CFSG.Quasithin.Vol2.KGHat.natCard_F4Space (act c₀) hz
  have hcard2 : Nat.card ↥U = 2 ^ finrank (ZMod 2) ↥U := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hd : finrank (ZMod 2) ↥U =
      2 * finrank CFSG.Fischer.F4 (CFSG.Quasithin.Vol2.KGHat.F4Space (act c₀) hz) := by
    apply Nat.pow_right_injective (le_refl 2)
    show 2 ^ finrank (ZMod 2) ↥U = 2 ^ (2 * _)
    rw [← hcard2, pow_mul]
    exact hcard4
  obtain ⟨m, hm⟩ := h3dvd
  have hU7 : finrank (ZMod 2) U ≤ 7 := by omega
  have hperf : commutator ↥(Xsub S a) = ⊤ := Group.isPerfect_def.1 hΓ
  have hs := isSimpleGroup_quotient_center_Xsub S h h217 h3 hα hpsu
  have hZcard : Nat.card (Subgroup.center ↥(Xsub S a)) = 3 := hZbcard ▸ hZb3
  obtain ⟨π, hπdef⟩ : ∃ π, π = rhoLinRestrict S (Xsub S a) U hUX := ⟨_, rfl⟩
  have hπker : π.ker ≠ ⊤ := by
    intro htop
    obtain ⟨x, hx, hxa⟩ := exists_rhoLin_aVec_ne S h h217 h3 hα hpsu
    have h1 : π ⟨x, hx⟩ = 1 := MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top _)
    apply hxa
    have := congrArg (fun f : ↥U ≃ₗ[ZMod 2] ↥U => ((f ⟨_, haU⟩ : ↥U) : Additive (QbarOf S))) h1
    rw [hπdef] at this
    exact this
  have hπZ : π.ker ⊓ Subgroup.center ↥(Xsub S a) = ⊥ := by
    have hdvd : Nat.card ↥(π.ker ⊓ Subgroup.center ↥(Xsub S a)) ∣ 3 :=
      hZcard ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3'
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : π.ker ⊓ Subgroup.center ↥(Xsub S a) = Subgroup.center ↥(Xsub S a) :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3', hZcard])
      have hc₀k : c₀ ∈ π.ker := (Subgroup.mem_inf.mp (heq.symm ▸ hc₀Z)).1
      apply hca
      have := congrArg (fun f : ↥U ≃ₗ[ZMod 2] ↥U => ((f ⟨_, haU⟩ : ↥U) : Additive (QbarOf S)))
        (MonoidHom.mem_ker.mp hc₀k)
      rw [hπdef] at this
      exact this
  have hinj := CFSG.GroupTheory.injective_of_ker_inf_center_eq_bot π hperf hs hπker hπZ
  obtain ⟨φ⟩ := nonempty_mulEquiv_U2 S h h217 h3 hα hpsu
  have hXcard : Nat.card ↥(Xsub S a) = 25920 * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(Xsub S a)),
      Nat.card_congr φ.toEquiv, CFSG.GH74.Exceptional.card_U2_four, hZcard]
  exact CFSG.GroupTheory.not_three_pow_five_dvd_card_linearEquiv_of_finrank_le_seven hU7
    (dvd_trans (by rw [hXcard]; norm_num) (Subgroup.card_dvd_of_injective π hinj))

theorem nonempty_Xsub_mulEquiv_U2 (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a)
    (hpsu : fischerCentralQuotientModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4) fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0))
    (hw : w ≤ 5) :
    Nonempty (↥(Xsub S a) ≃* U2 4) := by
  obtain ⟨φ⟩ := nonempty_mulEquiv_U2 S h h217 h3 hα hpsu
  exact ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq
    (center_Xsub_eq_bot S h h217 h3 hα hpsu hw)).symm).trans φ⟩

theorem isSimpleGroup_Xsub (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a)
    (hpsu : fischerCentralQuotientModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4) fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0))
    (hw : w ≤ 5) :
    IsSimpleGroup ↥(Xsub S a) := by
  have hs := isSimpleGroup_quotient_center_Xsub S h h217 h3 hα hpsu
  exact (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq
    (center_Xsub_eq_bot S h h217 h3 hα hpsu hw)).symm).isSimpleGroup

theorem orderOf_eq_three_and_zpowers_eq_centralizer_Xsub (S : Setting z E F) {a : G} {w : ℕ}
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
    {α : Hbar z} (hα : α ∈ Tset S a)
    (hpsu : fischerCentralQuotientModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4) fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0))
    (hw : w ≤ 5) {ρ : Hbar z} (hρC : ρ ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)))
    (hρ1 : ρ ≠ 1) :
    orderOf ρ = 3 ∧ Subgroup.zpowers ρ = Subgroup.centralizer (Xsub S a : Set (Hbar z)) :=
  (card_eq_three_of_odd_of_dvd_six (odd_card_centralizer_Xsub S h h217 h3 hα hpsu hw)
    (card_centralizer_Xsub_dvd_six S h h217) hρC hρ1).2

theorem rhoLin_ne_self_of_mem_centralizer (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a)
    (hpsu : fischerCentralQuotientModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4) fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0))
    (hw : w = 4) {ρ : Hbar z} (hρC : ρ ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)))
    (hρ1 : ρ ≠ 1) {v : Additive (QbarOf S)} (hv : v ≠ 0) : rhoLin S ρ v ≠ v := by
  classical
  have hw5 : w ≤ 5 := by omega
  obtain ⟨hρ3, hρC'⟩ :=
    orderOf_eq_three_and_zpowers_eq_centralizer_Xsub S h h217 h3 hα hpsu hw5 hρC hρ1
  have hρpow : ρ ^ 3 = 1 := hρ3 ▸ pow_orderOf_eq_one ρ
  have hCn : (Subgroup.centralizer (Xsub S a : Set (Hbar z))).Normal := inferInstance
  have hLρ : Lbar S a ≤ Subgroup.normalizer (Subgroup.zpowers ρ : Set (Hbar z)) := by
    rw [hρC', Subgroup.normalizer_eq_top_iff.mpr hCn]
    exact le_top
  obtain ⟨⟨α₀, hα₀R⟩, hα₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.Rbar_ne_bot
  have hα₀1' : α₀ ≠ 1 := fun h1 => hα₀1 (Subtype.ext h1)
  have hα₀X : α₀ ∈ Xsub S a :=
    subset_Xsub S a (Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hα₀R hα₀1'))
  have hρα : ρ * α₀ = α₀ * ρ := (Subgroup.mem_centralizer_iff.mp hρC α₀ hα₀X).symm
  have hsum := (aVec_add_rhoLin_add_rhoLin_eq_zero S h h217 hρpow hρ1 hLρ hα₀R hα₀1' hρα).1
  obtain ⟨hρa, haU, hz3⟩ := facts_of_aVec_add S h hρpow hsum
  have : Finite (Additive (QbarOf S)) := inferInstance
  have : Module.Finite (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  have hdim := finrank_QbarOf_eq_two_mul S h.card_F
  obtain ⟨U, hUdef⟩ : ∃ U, U = commSpace (rhoLin S ρ) := ⟨_, rfl⟩
  rw [← hUdef] at haU hz3
  have hUX : ∀ x ∈ Xsub S a, ∀ u ∈ U, rhoLin S x u ∈ U := fun x hx u hu => by
    rw [hUdef] at hu ⊢
    exact rhoLin_mem_commSpace_of_commute S (Subgroup.mem_centralizer_iff.mp hρC x hx) hu
  have hUρ : ∀ y ∈ Subgroup.zpowers ρ, ∀ u ∈ U, rhoLin S y u ∈ U := fun y hy u hu => by
    rw [hUdef] at hu ⊢
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact rhoLin_mem_commSpace_of_commute S ((Commute.refl ρ).zpow_left k).eq hu
  obtain ⟨π, hπdef⟩ : ∃ π, π = rhoLinRestrict S (Xsub S a) U hUX := ⟨_, rfl⟩
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = rhoLinRestrict S (Subgroup.zpowers ρ) U hUρ := ⟨_, rfl⟩
  have hcomm : ∀ (x : ↥(Xsub S a)) (y : ↥(Subgroup.zpowers ρ)), Commute (π x) (σ y) := by
    intro x y
    have hyC : (y : Hbar z) ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)) := hρC' ▸ y.2
    have hxy : (x : Hbar z) * y = y * x := Subgroup.mem_centralizer_iff.mp hyC x x.2
    show π x * σ y = σ y * π x
    refine LinearEquiv.ext fun u => Subtype.ext ?_
    rw [hπdef, hσdef]
    show rhoLin S x (rhoLin S y u) = rhoLin S y (rhoLin S x u)
    rw [← LinearEquiv.mul_apply, ← rhoLin_mul, hxy, rhoLin_mul, LinearEquiv.mul_apply]
  have hZ := center_Xsub_eq_bot S h h217 h3 hα hpsu hw5
  have hperf : commutator ↥(Xsub S a) = ⊤ :=
    Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 (commutator_Xsub S h h217 h3 hα hpsu))
  have hs := isSimpleGroup_quotient_center_Xsub S h h217 h3 hα hpsu
  have hπker : π.ker ≠ ⊤ := by
    intro htop
    obtain ⟨x, hx, hxa⟩ := exists_rhoLin_aVec_ne S h h217 h3 hα hpsu
    have h1 : π ⟨x, hx⟩ = 1 := MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top _)
    apply hxa
    have := congrArg (fun f : ↥U ≃ₗ[ZMod 2] ↥U => ((f ⟨_, haU⟩ : ↥U) : Additive (QbarOf S))) h1
    rw [hπdef] at this
    exact this
  have hπinj := CFSG.GroupTheory.injective_of_ker_inf_center_eq_bot π hperf hs hπker
    (by rw [hZ, inf_bot_eq])
  have hfact : Fact (Nat.card ↥(Subgroup.zpowers ρ)).Prime :=
    ⟨by rw [Nat.card_zpowers, hρ3]; exact Nat.prime_three⟩
  have hψinj : Function.Injective (π.noncommCoprod σ hcomm) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ hxy
    rw [MonoidHom.noncommCoprod_apply] at hxy
    have hπx : π x = (σ y)⁻¹ := eq_inv_of_mul_eq_one_left hxy
    have hxZ : x ∈ Subgroup.center ↥(Xsub S a) := by
      rw [Subgroup.mem_center_iff]
      intro x'
      apply hπinj
      rw [map_mul, map_mul, hπx]
      exact (hcomm x' y).inv_right.eq
    rw [hZ, Subgroup.mem_bot] at hxZ
    subst hxZ
    rw [map_one, one_mul] at hxy
    have hy : y = 1 := by
      rcases (σ.ker).eq_bot_or_eq_top_of_prime_card with hb | ht
      · have : y ∈ σ.ker := hxy
        rwa [hb, Subgroup.mem_bot] at this
      · exfalso
        have hρk : (⟨ρ, Subgroup.mem_zpowers ρ⟩ : ↥(Subgroup.zpowers ρ)) ∈ σ.ker :=
          ht ▸ Subgroup.mem_top _
        apply hρa
        have := congrArg (fun f : ↥U ≃ₗ[ZMod 2] ↥U => ((f ⟨_, haU⟩ : ↥U) : Additive (QbarOf S)))
          (MonoidHom.mem_ker.mp hρk)
        rw [hσdef] at this
        exact this
    rw [hy]
    rfl
  obtain ⟨φ⟩ := nonempty_mulEquiv_U2 S h h217 h3 hα hpsu
  have hXcard : Nat.card ↥(Xsub S a) = 25920 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(Xsub S a)),
      Nat.card_congr φ.toEquiv, CFSG.GH74.Exceptional.card_U2_four, hZ, Subgroup.card_bot,
      mul_one]
  have hdvd := Subgroup.card_dvd_of_injective _ hψinj
  rw [Nat.card_prod, hXcard, Nat.card_zpowers, hρ3] at hdvd
  have hU8 : 8 ≤ finrank (ZMod 2) U := by
    by_contra hlt
    exact CFSG.GroupTheory.not_three_pow_five_dvd_card_linearEquiv_of_finrank_le_seven
      (by omega) (dvd_trans (by norm_num) hdvd)
  have hUtop : U = ⊤ := Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le U)
    (by omega))
  intro hfix
  have := hz3 v (hUtop ▸ Submodule.mem_top)
  rw [hfix, hfix] at this
  have hvv : v + v = 0 := by rw [← sub_eq_add_vec (ZMod 2), sub_self]
  rw [hvv] at this
  exact hv this

end Sec4PSUEnd

end CFSG.RankThree.GF2n.Stroth78
