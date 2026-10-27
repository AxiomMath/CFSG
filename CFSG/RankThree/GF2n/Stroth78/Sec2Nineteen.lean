module

public import CFSG.RankThree.GF2n.Stroth78.Sec3One
public import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeZQ

import CFSG.RankThree.GF2n.Stroth78.Sec2Six
import CFSG.RankThree.GF2n.Stroth78.Sec2SixteenReverse

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem rhoZ_Lbar_eq_self_of_forall_Rbar (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (hR : ∀ r ∈ Rbar S a, (∀ u : ↥(ZQ z), rhoZ S r u = u) → r = 1)
    {v : ↥(ZQ z)} (hv : ∀ r ∈ Rbar S a, rhoZ S r v = v)
    {l : Hbar z} (hl : l ∈ Lbar S a) : rhoZ S l v = v := by
  classical
  have hvQ : (v : G) ∈ Q z := (Subgroup.mem_inf.mp v.2).1
  have hvC : ∀ q ∈ Q z, q * (v : G) = (v : G) * q := fun q hq =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp v.2).2 q hq)
  have hZaH : ∀ y ∈ centerIn (QaOf a), y ∈ H z := by
    intro y hy
    rw [H, Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst t
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 z h.mem_Qa
  have hvZa : ∀ y ∈ centerIn (QaOf a), y * (v : G) * y⁻¹ = v := by
    intro y hy
    have hyR : (QuotientGroup.mk ⟨y, hZaH y hy⟩ : Hbar z) ∈ Rbar S a :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hy, hZaH y hy⟩)))
    have := rhoZ_mk S ⟨y, hZaH y hy⟩ v
    rw [hv _ hyR] at this
    exact this.symm
  suffices hLa : ∀ x ∈ La S a, x * (v : G) * x⁻¹ = v by
    obtain ⟨x, hx, rfl⟩ := hl
    apply Subtype.ext
    rw [QuotientGroup.mk'_apply, rhoZ_mk]
    exact hLa x (Subgroup.mem_subgroupOf.mp hx)
  have hcent : ∀ x : G, x * (v : G) * x⁻¹ = v ↔ x ∈ Subgroup.centralizer ({(v : G)} : Set G) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      calc x * (v : G) = x * (v : G) * x⁻¹ * x := by group
        _ = v * x := by rw [hx]
    · intro hx
      rw [hx]
      group
  intro x hx
  rw [hcent]
  revert x
  rw [← SetLike.le_def]
  apply sup_le
  · intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hvC q hq
  · by_cases hvQa : (v : G) ∈ QaOf a
    ·
      rintro y ⟨hyQa, hyH⟩
      obtain ⟨g, hg⟩ := isConj_iff.mp h.isConj
      have hcomm_mem : ⁅y, (v : G)⁆ ∈ Subgroup.zpowers a := by
        rw [← commutator_QaOf_eq_zpowers S hg]
        exact Subgroup.commutator_mem_commutator hyQa hvQa
      have hyvQ : y * (v : G) * y⁻¹ ∈ Q z := fStar_normal (M := H z) hyH hvQ
      have hyvZ : y * (v : G) * y⁻¹ ∈ ZQ z := by
        refine Subgroup.mem_inf.mpr ⟨hyvQ, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro q hq
        have hq' : y⁻¹ * q * y ∈ Q z := by
          have := fStar_normal (M := H z) (inv_mem hyH) hq
          rwa [inv_inv] at this
        have := hvC _ hq'
        calc q * (y * (v : G) * y⁻¹) = y * ((y⁻¹ * q * y) * v) * y⁻¹ := by group
          _ = y * (v * (y⁻¹ * q * y)) * y⁻¹ := by rw [this]
          _ = y * (v : G) * y⁻¹ * q := by group
      have hcommZ : ⁅y, (v : G)⁆ ∈ ZQ z := by
        rw [commutatorElement_def]
        exact mul_mem hyvZ (inv_mem v.2)
      have ha2 : a ^ 2 = 1 := sq_eq_one_of_isConj S h.isConj
      have hcomm1 : ⁅y, (v : G)⁆ = 1 := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcomm_mem
        obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
        · rw [← hk, zpow_mul]
          simp [ha2]
        · exfalso
          apply h.not_mem_ZQ
          have : a ^ (2 * m + 1) = a := by
            rw [zpow_add, zpow_mul]
            simp [ha2]
          rw [← this, hk]
          exact hcommZ
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact commutatorElement_eq_one_iff_mul_comm.mp hcomm1
    ·
      exfalso
      obtain ⟨g, hgQaz, hga⟩ :=
        exists_conj_eq_z_of_mem_QaOf_mul_z S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
      have hgz : g * z * g⁻¹ = a := conj_z_eq_of_conj_a_eq S h.mem_Q h.isConj h.not_mem_ZQ hgQaz hga
      set u : G := g * (v : G) * g⁻¹ with hu
      have hva : (v : G) * a = a * v := (hvC a h.mem_Q).symm
      have huH : u ∈ H z := by
        rw [H, Subgroup.mem_centralizer_iff]
        intro t ht
        rw [Set.mem_singleton_iff] at ht
        subst t
        rw [← hga, hu]
        calc g * a * g⁻¹ * (g * (v : G) * g⁻¹) = g * (a * v) * g⁻¹ := by group
          _ = g * (v * a) * g⁻¹ := by rw [hva]
          _ = g * (v : G) * g⁻¹ * (g * a * g⁻¹) := by group
      have hQa_map : (Q z).map (MulAut.conj g).toMonoidHom = QaOf a := by
        rw [show Q z = QaOf z from rfl, map_conj_QaOf z g, hgz]
      have hQ_map : (QaOf a).map (MulAut.conj g).toMonoidHom = Q z := by
        rw [map_conj_QaOf a g, hga]
      have huQa : u ∈ QaOf a := by
        rw [← hQa_map]
        exact ⟨v, hvQ, rfl⟩
      have huZa : u ∈ centerIn (QaOf a) := by
        refine Subgroup.mem_inf.mpr ⟨huQa, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [← hQa_map] at hy
        obtain ⟨q, hq, rfl⟩ := hy
        change g * q * g⁻¹ * (g * (v : G) * g⁻¹) = g * (v : G) * g⁻¹ * (g * q * g⁻¹)
        calc g * q * g⁻¹ * (g * (v : G) * g⁻¹) = g * (q * v) * g⁻¹ := by group
          _ = g * (v * q) * g⁻¹ := by rw [hvC q hq]
          _ = g * (v : G) * g⁻¹ * (g * q * g⁻¹) := by group
      have huZQ : ∀ c ∈ ZQ z, u * c * u⁻¹ = c := by
        intro c hc
        have hcZa : g⁻¹ * c * g ∈ centerIn (QaOf a) := by
          have hcQ : c ∈ Q z := (Subgroup.mem_inf.mp hc).1
          rw [← hQ_map] at hcQ
          obtain ⟨y, hy, hyc⟩ := hcQ
          have hyc' : g⁻¹ * c * g = y := by
            rw [← hyc]
            change g⁻¹ * (g * y * g⁻¹) * g = y
            group
          rw [hyc']
          refine Subgroup.mem_inf.mpr ⟨hy, ?_⟩
          rw [Subgroup.mem_centralizer_iff]
          intro t ht
          have htQ : g * t * g⁻¹ ∈ Q z := by
            rw [← hQ_map]
            exact ⟨t, ht, rfl⟩
          have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 _ htQ
          rw [← hyc] at h1
          change g * t * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * t * g⁻¹) at h1
          have h2 : g * (t * y) * g⁻¹ = g * (y * t) * g⁻¹ := by
            calc g * (t * y) * g⁻¹ = g * t * g⁻¹ * (g * y * g⁻¹) := by group
              _ = g * y * g⁻¹ * (g * t * g⁻¹) := h1
              _ = g * (y * t) * g⁻¹ := by group
          exact mul_left_cancel (mul_right_cancel h2)
        have h1 := hvZa _ hcZa
        have hc' : (v : G) * (g⁻¹ * c * g) = (g⁻¹ * c * g) * v := by
          calc (v : G) * (g⁻¹ * c * g)
              = ((g⁻¹ * c * g) * v * (g⁻¹ * c * g)⁻¹) * (g⁻¹ * c * g) := by rw [h1]
            _ = (g⁻¹ * c * g) * v := by group
        calc u * c * u⁻¹ = g * ((v : G) * (g⁻¹ * c * g)) * (v : G)⁻¹ * g⁻¹ := by rw [hu]; group
          _ = g * ((g⁻¹ * c * g) * v) * (v : G)⁻¹ * g⁻¹ := by rw [hc']
          _ = c := by group
      have huQ : u ∉ Q z := by
        intro huQ
        apply hvQa
        rw [← hQ_map] at huQ
        obtain ⟨y, hy, hyu⟩ := huQ
        have : y = v := by
          have := hyu
          change g * y * g⁻¹ = g * (v : G) * g⁻¹ at this
          exact mul_left_cancel (mul_right_cancel this)
        rw [← this]
        exact hy
      have huR : (QuotientGroup.mk ⟨u, huH⟩ : Hbar z) ∈ Rbar S a :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
          (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨huZa, huH⟩)))
      have htriv : ∀ c : ↥(ZQ z), rhoZ S (QuotientGroup.mk ⟨u, huH⟩) c = c := by
        intro c
        apply Subtype.ext
        rw [rhoZ_mk]
        exact huZQ c c.2
      have h1 := hR _ huR htriv
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      exact huQ h1

theorem forall_Rbar_eq_one_of_rhoZ_Xsub (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (hX : ∃ x ∈ Xsub S a, rhoZ S x ≠ 1) :
    ∀ r ∈ Rbar S a, (∀ u : ↥(ZQ z), rhoZ S r u = u) → r = 1 := by
  intro r hr hrZ
  by_contra hr1
  have hr1' : rhoZ S r = 1 := MulEquiv.ext hrZ
  have hrE : r ∈ Eset S a := Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hr hr1)
  obtain ⟨-, -, -, hconj⟩ := stroth78_31 S h h217
  have hE : Eset S a ⊆ ((rhoZ S).ker : Set (Hbar z)) := by
    intro e he
    obtain ⟨x, -, rfl⟩ := (hconj r hrE e).mp he
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_mul, hr1', mul_one, map_inv,
      mul_inv_cancel]
  have hXk : Xsub S a ≤ (rhoZ S).ker := (Subgroup.closure_le _).mpr hE
  obtain ⟨x, hxX, hx1⟩ := hX
  exact hx1 (MonoidHom.mem_ker.mp (hXk hxX))

end CFSG.RankThree.GF2n.Stroth78
