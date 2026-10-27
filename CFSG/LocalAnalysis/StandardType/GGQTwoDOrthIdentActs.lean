module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDShared
public import CFSG.LocalAnalysis.StandardType.GGQTwoDStdModel
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
public import CFSG.LocalAnalysis.StandardType.GGOrthFramePairs
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameTransport
public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthPathsDefs
import CFSG.LocalAnalysis.StandardType.GGOrthFrameModelAux

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.OrthTorus CFSG.Open CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.PhanDn.QTwo CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits
open CFSG.RankThree.Classical2 (orthDerived)

section Ident

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs Y : Subgroup G}
  (Φ : OrthFrameCore p Bs Y)

private theorem pmoi_hp3 (hF : Nat.card Φ.F = 2) : p = 3 := by
  have h := Φ.hpq
  rw [hF] at h
  exact (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp h

private theorem pmoi_exists_inner_w {ρ : MulAut ↥Bs} (hρ : ρ ∈ ggAutomizer Y Bs) :
    ∃ w : ↥(orthDerived Φ.Q),
      ∀ b : ↥Bs, ((ρ b : ↥Bs) : G) = Φ.ψ w * b * (Φ.ψ w)⁻¹ := by
  obtain ⟨g, _hgY, _hgN, hg⟩ := mem_ggAutomizer_iff.mp hρ
  have hg' : g ∈ Φ.ψ.range := by rwa [Φ.hrange]
  obtain ⟨w, hw⟩ := hg'
  refine ⟨w, fun b => ?_⟩
  rw [hw]
  exact hg b

private theorem pmoi_acts_iff_conj (hZ : Subgroup.center ↥(orthDerived Φ.Q) = ⊥)
    {ρ : MulAut ↥Bs} (w : ↥(orthDerived Φ.Q))
    (hwr : ∀ b : ↥Bs, ((ρ b : ↥Bs) : G) = Φ.ψ w * b * (Φ.ψ w)⁻¹) (x : OmPlusIdx Φ.r) :
    Φ.Acts ρ x ↔ ∀ f, (w : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
      Φ.Δ.τ (omPlusRefl p x f) := by
  constructor
  · intro hacts f
    obtain ⟨b, hb⟩ := Φ.hβsurj (Φ.Δ.τ f) (le_of_eq Φ.Δ.τ_range ⟨f, rfl⟩)
    have hv := congrArg Subtype.val (Φ.beta_equivariant_of_inner hZ w ρ hwr b)
    change (Φ.β (ρ b) : Φ.V ≃ₗ[Φ.F] Φ.V) =
      (w : Φ.V ≃ₗ[Φ.F] Φ.V) * (Φ.β b : Φ.V ≃ₗ[Φ.F] Φ.V) *
        (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ at hv
    rw [hb] at hv
    exact hv.symm.trans (hacts b f hb)
  · intro hconj b f hbf
    have hv := congrArg Subtype.val (Φ.beta_equivariant_of_inner hZ w ρ hwr b)
    change (Φ.β (ρ b) : Φ.V ≃ₗ[Φ.F] Φ.V) =
      (w : Φ.V ≃ₗ[Φ.F] Φ.V) * (Φ.β b : Φ.V ≃ₗ[Φ.F] Φ.V) *
        (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ at hv
    rw [hv, hbf, hconj f]

private theorem pmoi_eqLocus_omPlusRefl_false (p r : ℕ) {i j : Fin r} (hij : i < j) :
    MonoidHom.eqLocus (omPlusRefl p (⟨(i, j), hij⟩, false)).toMonoidHom (MonoidHom.id _) =
      reflFixedCoord p r i j := by
  ext f
  constructor
  · intro hf
    rw [ggOFM_mem_reflFixedCoord_iff]
    change omPlusRefl p (⟨(i, j), hij⟩, false) f = f at hf
    rw [omPlusRefl_false] at hf
    exact ggOFM_eq_of_permAut_swap_eq_self hf
  · intro hf
    change omPlusRefl p (⟨(i, j), hij⟩, false) f = f
    rw [omPlusRefl_false]
    exact ggOFM_permAut_swap_eq_self_of_eq ((ggOFM_mem_reflFixedCoord_iff f).mp hf)

private theorem pmoi_eqLocus_omPlusRefl_true (p r : ℕ) {i j : Fin r} (hij : i < j) :
    MonoidHom.eqLocus (omPlusRefl p (⟨(i, j), hij⟩, true)).toMonoidHom (MonoidHom.id _) =
      reflFixedCoordPos p r i j := by
  ext f
  constructor
  · intro hf
    rw [ggOFM_mem_reflFixedCoordPos_iff]
    change omPlusRefl p (⟨(i, j), hij⟩, true) f = f at hf
    rw [funext_iff] at hf
    have hi := hf i
    rw [omPlusRefl_apply_coord, if_pos rfl] at hi
    simp only [Bool.cond_true] at hi
    rw [← hi, inv_mul_cancel]
  · intro hf
    change omPlusRefl p (⟨(i, j), hij⟩, true) f = f
    rw [funext_iff]
    intro k
    rw [omPlusRefl_apply_coord]
    have hpos := (ggOFM_mem_reflFixedCoordPos_iff f).mp hf
    by_cases hk : k = i
    · subst hk
      rw [if_pos rfl]
      simp only [Bool.cond_true]
      exact (mul_eq_one_iff_eq_inv.mp hpos).symm
    · by_cases hk' : k = j
      · subst hk'
        rw [if_neg hk, if_pos rfl]
        simp only [Bool.cond_true]
        exact mul_eq_one_iff_inv_eq.mp hpos
      · rw [if_neg hk, if_neg hk']

private theorem pmoi_fixTorus_eq (x : OmPlusIdx Φ.r) :
    Φ.fixTorus x = if x.2 then Φ.Δ.reflFixedPos x.1.1.1 x.1.1.2
      else Φ.Δ.reflFixed x.1.1.1 x.1.1.2 := by
  rcases x with ⟨⟨⟨i, j⟩, hij⟩, s⟩
  cases s
  · unfold OrthFrameCore.fixTorus TBJOmData.reflFixed
    rw [pmoi_eqLocus_omPlusRefl_false p Φ.r hij, if_neg (by simp)]
  · unfold OrthFrameCore.fixTorus TBJOmData.reflFixedPos
    rw [pmoi_eqLocus_omPlusRefl_true p Φ.r hij, if_pos (by simp)]

private theorem pmoi_rank1_eq (x : OmPlusIdx Φ.r) :
    Φ.rank1 x = if x.2 then Φ.Δ.rankOnePos x.1.1.1 x.1.1.2
      else Φ.Δ.rankOne x.1.1.1 x.1.1.2 := by
  rcases x with ⟨⟨⟨i, j⟩, hij⟩, s⟩
  cases s
  · have hfix : Φ.fixTorus (⟨⟨⟨i, j⟩, hij⟩, false⟩) = Φ.Δ.reflFixed i j := by
      have h := pmoi_fixTorus_eq Φ (⟨⟨⟨i, j⟩, hij⟩, false⟩)
      rw [if_neg (by simp)] at h
      exact h
    unfold OrthFrameCore.rank1 TBJOmData.rankOne
    rw [hfix, inf_comm, if_neg (by simp)]
  · have hfix : Φ.fixTorus (⟨⟨⟨i, j⟩, hij⟩, true⟩) = Φ.Δ.reflFixedPos i j := by
      have h := pmoi_fixTorus_eq Φ (⟨⟨⟨i, j⟩, hij⟩, true⟩)
      rw [if_pos (by simp)] at h
      exact h
    unfold OrthFrameCore.rank1 TBJOmData.rankOnePos
    rw [hfix, inf_comm, if_pos (by simp)]

private theorem pmoi_comm_of_mem_fixTorus {w : ↥(orthDerived Φ.Q)} {x : OmPlusIdx Φ.r}
    (hw : ∀ f, (w : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
      Φ.Δ.τ (omPlusRefl p x f)) :
    ∀ t ∈ Φ.fixTorus x,
      (w : Φ.V ≃ₗ[Φ.F] Φ.V) * t = t * (w : Φ.V ≃ₗ[Φ.F] Φ.V) := by
  intro t ht
  rw [OrthFrameCore.fixTorus, Subgroup.mem_map] at ht
  obtain ⟨f, hf, rfl⟩ := ht
  change omPlusRefl p x f = f at hf
  have h := hw f
  rw [hf] at h
  exact (mul_inv_eq_iff_eq_mul).mp h

theorem qtwoOrth_exists_acts_core (hF : Nat.card Φ.F = 2) {ρ : MulAut ↥Bs}
    (hρ : ρ ∈ ggAutomizer Y Bs) (hr : GGIsReflection p ρ) : ∃ x : OmPlusIdx Φ.r, Φ.Acts ρ x := by
  have hp3 := pmoi_hp3 Φ hF
  have hp2 : p ≠ 2 := by omega
  have hQ := Φ.Δ.polarBilin_nondegenerate_of_noFixed Φ.hfix
  have hdim := Φ.Δ.finrank_eq_two_mul_of_noFixed Φ.hfix
  have hT := CFSG.RankThree.PartOne.exists_threeSingular_of_dim Φ.Q hQ Φ.hr hdim
  have : Nontrivial Φ.V := CFSG.RankThree.PartOne.nontrivial_of_threeSingular hT
  have hZ' := CFSG.RankThree.PartOne.center_orthDerived_eq_bot hQ hT
  obtain ⟨w, hwr⟩ := pmoi_exists_inner_w Φ hρ
  obtain ⟨x, hx⟩ := Φ.exists_signed_action_of_inner hp2 hQ hZ' w ρ hwr hr
  exact ⟨x, (pmoi_acts_iff_conj Φ hZ' w hwr x).mpr hx⟩

theorem qtwoOrth_acts_injective_core (hF : Nat.card Φ.F = 2) {ρ ρ' : MulAut ↥Bs}
    (hρ : ρ ∈ ggAutomizer Y Bs) (hρ' : ρ' ∈ ggAutomizer Y Bs) {x : OmPlusIdx Φ.r}
    (hx : Φ.Acts ρ x) (hx' : Φ.Acts ρ' x) : ρ = ρ' := by
  have hQ := Φ.Δ.polarBilin_nondegenerate_of_noFixed Φ.hfix
  have hdim := Φ.Δ.finrank_eq_two_mul_of_noFixed Φ.hfix
  have hT := CFSG.RankThree.PartOne.exists_threeSingular_of_dim Φ.Q hQ Φ.hr hdim
  have : Nontrivial Φ.V := CFSG.RankThree.PartOne.nontrivial_of_threeSingular hT
  have hZ' := CFSG.RankThree.PartOne.center_orthDerived_eq_bot hQ hT
  obtain ⟨w, hwr⟩ := pmoi_exists_inner_w Φ hρ
  obtain ⟨v, hvr⟩ := pmoi_exists_inner_w Φ hρ'
  have hw := (pmoi_acts_iff_conj Φ hZ' w hwr x).mp hx
  have hv := (pmoi_acts_iff_conj Φ hZ' v hvr x).mp hx'
  exact (Φ.aut_eq_iff_torus_action w v ρ ρ' (omPlusRefl p x) (omPlusRefl p x)
    hwr hvr hw hv).mpr rfl

theorem qtwoOrth_comm_iff_core (hF : Nat.card Φ.F = 2) {ρ ρ' : MulAut ↥Bs}
    (hρ : ρ ∈ ggAutomizer Y Bs) (hρ' : ρ' ∈ ggAutomizer Y Bs) {x y : OmPlusIdx Φ.r}
    (hx : Φ.Acts ρ x) (hy : Φ.Acts ρ' y) :
    ρ * ρ' = ρ' * ρ ↔ omPlusRefl p x * omPlusRefl p y = omPlusRefl p y * omPlusRefl p x := by
  have hQ := Φ.Δ.polarBilin_nondegenerate_of_noFixed Φ.hfix
  have hdim := Φ.Δ.finrank_eq_two_mul_of_noFixed Φ.hfix
  have hT := CFSG.RankThree.PartOne.exists_threeSingular_of_dim Φ.Q hQ Φ.hr hdim
  have : Nontrivial Φ.V := CFSG.RankThree.PartOne.nontrivial_of_threeSingular hT
  have hZ' := CFSG.RankThree.PartOne.center_orthDerived_eq_bot hQ hT
  obtain ⟨w, hwr⟩ := pmoi_exists_inner_w Φ hρ
  obtain ⟨v, hvr⟩ := pmoi_exists_inner_w Φ hρ'
  have hw := (pmoi_acts_iff_conj Φ hZ' w hwr x).mp hx
  have hv := (pmoi_acts_iff_conj Φ hZ' v hvr y).mp hy
  exact Φ.aut_commute_iff_torus_action w v ρ ρ' (omPlusRefl p x) (omPlusRefl p y)
    hwr hvr hw hv

theorem qtwoOrth_rankOneIn_core (hF : Nat.card Φ.F = 2) {ρ : MulAut ↥Bs}
    (hρ : ρ ∈ ggAutomizer Y Bs) (hr : GGIsReflection p ρ) {x : OmPlusIdx Φ.r}
    (hx : Φ.Acts ρ x) : ggRankOneIn Y Bs ρ = Φ.img (Φ.rank1 x) := by
  have hQ := Φ.Δ.polarBilin_nondegenerate_of_noFixed Φ.hfix
  have hdim := Φ.Δ.finrank_eq_two_mul_of_noFixed Φ.hfix
  have hT := CFSG.RankThree.PartOne.exists_threeSingular_of_dim Φ.Q hQ Φ.hr hdim
  have : Nontrivial Φ.V := CFSG.RankThree.PartOne.nontrivial_of_threeSingular hT
  have hZ' := CFSG.RankThree.PartOne.center_orthDerived_eq_bot hQ hT
  obtain ⟨w, hwr⟩ := pmoi_exists_inner_w Φ hρ
  have hw := (pmoi_acts_iff_conj Φ hZ' w hwr x).mp hx
  rw [Φ.rankOne_eq_map_of_signed_action w ρ x hwr hw, pmoi_rank1_eq Φ x]
  rfl

theorem qtwoOrth_rankTwoIn_core (hF : Nat.card Φ.F = 2) {ρ ρ' : MulAut ↥Bs}
    (hρ : ρ ∈ ggAutomizer Y Bs) (hρ' : ρ' ∈ ggAutomizer Y Bs) (hr : GGIsReflection p ρ)
    (hr' : GGIsReflection p ρ') {x y : OmPlusIdx Φ.r} (hx : Φ.Acts ρ x) (hy : Φ.Acts ρ' y)
    (hnc : ρ * ρ' ≠ ρ' * ρ) : ggRankTwoIn Y Bs ρ ρ' = Φ.img (Φ.rank2 x y) := by
  have hQ := Φ.Δ.polarBilin_nondegenerate_of_noFixed Φ.hfix
  have hdim := Φ.Δ.finrank_eq_two_mul_of_noFixed Φ.hfix
  have hT := CFSG.RankThree.PartOne.exists_threeSingular_of_dim Φ.Q hQ Φ.hr hdim
  have : Nontrivial Φ.V := CFSG.RankThree.PartOne.nontrivial_of_threeSingular hT
  have hZ' := CFSG.RankThree.PartOne.center_orthDerived_eq_bot hQ hT
  obtain ⟨w, hwr⟩ := pmoi_exists_inner_w Φ hρ
  obtain ⟨v, hvr⟩ := pmoi_exists_inner_w Φ hρ'
  have hw := (pmoi_acts_iff_conj Φ hZ' w hwr x).mp hx
  have hv := (pmoi_acts_iff_conj Φ hZ' v hvr y).mp hy
  let β' : ↥Bs →* (Φ.V ≃ₗ[Φ.F] Φ.V) := (orthDerived Φ.Q).subtype.comp Φ.β
  let H : Subgroup ↥Bs := MonoidHom.eqLocus (ρ : ↥Bs →* ↥Bs) (MonoidHom.id _) ⊓
    MonoidHom.eqLocus (ρ' : ↥Bs →* ↥Bs) (MonoidHom.id _)
  have hpres : ∀ (b : ↥Bs) (z : ↥(orthDerived Φ.Q)),
      β' b * (z : Φ.V ≃ₗ[Φ.F] Φ.V) * (β' b)⁻¹ ∈ orthDerived Φ.Q :=
    fun b z => (orthDerived Φ.Q).mul_mem ((orthDerived Φ.Q).mul_mem (Φ.β b).2 z.2)
      ((orthDerived Φ.Q).inv_mem (Φ.β b).2)
  have hcompat : ∀ (b : ↥Bs) (z : ↥(orthDerived Φ.Q)),
      Φ.ψ ⟨β' b * (z : Φ.V ≃ₗ[Φ.F] Φ.V) * (β' b)⁻¹, hpres b z⟩ =
        (b : G) * Φ.ψ z * (b : G)⁻¹ := by
    intro b z
    have hz : (⟨β' b * (z : Φ.V ≃ₗ[Φ.F] Φ.V) * (β' b)⁻¹, hpres b z⟩ :
        ↥(orthDerived Φ.Q)) = Φ.β b * z * (Φ.β b)⁻¹ := Subtype.ext rfl
    rw [hz]
    exact Φ.hcompat b z
  have hmapH : H.map β' = Φ.fixTorus x ⊓ Φ.fixTorus y := by
    change (MonoidHom.eqLocus (ρ : ↥Bs →* ↥Bs) (MonoidHom.id _) ⊓
      MonoidHom.eqLocus (ρ' : ↥Bs →* ↥Bs) (MonoidHom.id _)).map β' =
        Φ.fixTorus x ⊓ Φ.fixTorus y
    apply le_antisymm
    · rintro t ⟨b, hb, rfl⟩
      change b ∈ ((ρ : ↥Bs →* ↥Bs).eqLocus (MonoidHom.id ↥Bs) ⊓
        (ρ' : ↥Bs →* ↥Bs).eqLocus (MonoidHom.id ↥Bs)) at hb
      rw [Subgroup.mem_inf] at hb
      have hg1 : (b : G) ∈ ggHyperplane Bs ρ :=
        Subgroup.mem_map.mpr ⟨b, hb.1, rfl⟩
      have hg2 : (b : G) ∈ ggHyperplane Bs ρ' :=
        Subgroup.mem_map.mpr ⟨b, hb.2, rfl⟩
      refine ⟨?_, ?_⟩
      · have := Φ.beta_mem_fixedTorus_of_hyperplane w ρ x hwr hw b hg1
        rwa [← pmoi_fixTorus_eq Φ x] at this
      · have := Φ.beta_mem_fixedTorus_of_hyperplane v ρ' y hvr hv b hg2
        rwa [← pmoi_fixTorus_eq Φ y] at this
    · intro t ht
      have hfix_le_A : Φ.fixTorus x ≤ Φ.A := by
        intro s hs
        rw [OrthFrameCore.fixTorus, Subgroup.mem_map] at hs
        obtain ⟨f, -, rfl⟩ := hs
        exact le_of_eq Φ.Δ.τ_range (MonoidHom.mem_range.mpr ⟨f, rfl⟩)
      obtain ⟨b, hb⟩ := Φ.hβsurj t (hfix_le_A ht.1)
      have htx : (Φ.β b : Φ.V ≃ₗ[Φ.F] Φ.V) ∈ Φ.fixTorus x := by rw [hb]; exact ht.1
      have hty : (Φ.β b : Φ.V ≃ₗ[Φ.F] Φ.V) ∈ Φ.fixTorus y := by rw [hb]; exact ht.2
      have hcommx := pmoi_comm_of_mem_fixTorus Φ hw (Φ.β b) htx
      have hcommy := pmoi_comm_of_mem_fixTorus Φ hv (Φ.β b) hty
      have hconjx : Φ.ψ w * (b : G) * (Φ.ψ w)⁻¹ = (b : G) :=
        (psi_conj_eq_iff Φ.ψ Φ.β Φ.hinj Φ.hcompat w b).mpr (Subtype.ext hcommx)
      have hconjy : Φ.ψ v * (b : G) * (Φ.ψ v)⁻¹ = (b : G) :=
        (psi_conj_eq_iff Φ.ψ Φ.β Φ.hinj Φ.hcompat v b).mpr (Subtype.ext hcommy)
      have hrb : ρ b = b := by
        apply Subtype.ext
        rw [hwr b]
        exact hconjx
      have hrb' : ρ' b = b := by
        apply Subtype.ext
        rw [hvr b]
        exact hconjy
      exact ⟨b, by
        change b ∈ ((ρ : ↥Bs →* ↥Bs).eqLocus (MonoidHom.id ↥Bs) ⊓
          (ρ' : ↥Bs →* ↥Bs).eqLocus (MonoidHom.id ↥Bs))
        rw [Subgroup.mem_inf]
        exact ⟨hrb, hrb'⟩, hb⟩
  have hmapG : H.map Bs.subtype = ggHyperplane Bs ρ ⊓ ggHyperplane Bs ρ' := by
    rw [Subgroup.map_inf _ _ _ Bs.subtype_injective]
    rfl
  have hpair := map_oTwoPrime_centralizer_of_normalizer_action Φ.ψ Φ.hinj Bs.subtype β'
    hpres hcompat H
  rw [ggRankTwoIn]
  conv_lhs => rw [← Φ.hrange]
  rw [← hmapG, ← hpair, hmapH]
  rfl

theorem qtwoOrth_exists_acts (hF : Nat.card Φ.F = 2)
    (hZ : Subgroup.center ↥Y = ⊥) (hBs : IsElemAbelian p Bs) {ρ : MulAut ↥Bs}
    (hρ : ρ ∈ ggAutomizer Y Bs) (hr : GGIsReflection p ρ) : ∃ x : OmPlusIdx Φ.r, Φ.Acts ρ x :=
  qtwoOrth_exists_acts_core Φ hF hρ hr

theorem qtwoOrth_acts_injective (hF : Nat.card Φ.F = 2)
    (hZ : Subgroup.center ↥Y = ⊥) (hBs : IsElemAbelian p Bs) {ρ ρ' : MulAut ↥Bs}
    (hρ : ρ ∈ ggAutomizer Y Bs) (hρ' : ρ' ∈ ggAutomizer Y Bs) {x : OmPlusIdx Φ.r}
    (hx : Φ.Acts ρ x) (hx' : Φ.Acts ρ' x) : ρ = ρ' :=
  qtwoOrth_acts_injective_core Φ hF hρ hρ' hx hx'

theorem qtwoOrth_comm_iff (hF : Nat.card Φ.F = 2)
    (hZ : Subgroup.center ↥Y = ⊥) (hBs : IsElemAbelian p Bs) {ρ ρ' : MulAut ↥Bs}
    (hρ : ρ ∈ ggAutomizer Y Bs) (hρ' : ρ' ∈ ggAutomizer Y Bs) {x y : OmPlusIdx Φ.r}
    (hx : Φ.Acts ρ x) (hy : Φ.Acts ρ' y) :
    ρ * ρ' = ρ' * ρ ↔ omPlusRefl p x * omPlusRefl p y = omPlusRefl p y * omPlusRefl p x :=
  qtwoOrth_comm_iff_core Φ hF hρ hρ' hx hy

theorem qtwoOrth_rankTwoIn (hF : Nat.card Φ.F = 2)
    (hZ : Subgroup.center ↥Y = ⊥) (hBs : IsElemAbelian p Bs) {ρ ρ' : MulAut ↥Bs}
    (hρ : ρ ∈ ggAutomizer Y Bs) (hρ' : ρ' ∈ ggAutomizer Y Bs) (hr : GGIsReflection p ρ)
    (hr' : GGIsReflection p ρ') {x y : OmPlusIdx Φ.r} (hx : Φ.Acts ρ x) (hy : Φ.Acts ρ' y)
    (hnc : ρ * ρ' ≠ ρ' * ρ) : ggRankTwoIn Y Bs ρ ρ' = Φ.img (Φ.rank2 x y) :=
  qtwoOrth_rankTwoIn_core Φ hF hρ hρ' hr hr' hx hy hnc

end Ident

end CFSG.StandardType.QTwo

end
