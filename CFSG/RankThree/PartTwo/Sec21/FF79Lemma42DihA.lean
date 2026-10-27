module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42MFacts
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

set_option synthInstance.maxSize 20000 in
set_option synthInstance.maxHeartbeats 1000000 in
private theorem s5CenV4 :
    ∀ a c : Equiv.Perm (Fin 5), a * a = 1 → c * c = 1 → a ≠ 1 → c ≠ 1 → a ≠ c →
      a * c = c * a → Equiv.Perm.sign a = 1 → Equiv.Perm.sign c = 1 →
      ∀ g : Equiv.Perm (Fin 5), g * a = a * g → g * c = c * g →
        g = 1 ∨ g = a ∨ g = c ∨ g = a * c := by
  decide +kernel

variable {G : Type} [Group G]

theorem m42_aut_V4 {L : Subgroup G} (hL : M42A5 L) {u v : G} (hu : u ∈ L) (hv : v ∈ L)
    (hu2 : u * u = 1) (hv2 : v * v = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v)
    (hc : u * v = v * u) {w : G} (hw : ∀ x ∈ L, w * x * w⁻¹ ∈ L)
    (hw' : ∀ x ∈ L, w⁻¹ * x * w ∈ L) (hwu : w * u = u * w) (hwv : w * v = v * w) :
    ∃ t ∈ ({1, u, v, u * v} : Set G), ∀ l ∈ L, w * l * w⁻¹ = t * l * t⁻¹ := by
  obtain ⟨eL⟩ := hL
  let φ : ↥L ≃* ↥L :=
    { toFun := fun d => ⟨w * d.1 * w⁻¹, hw d.1 d.2⟩
      invFun := fun d => ⟨w⁻¹ * d.1 * w, hw' d.1 d.2⟩
      left_inv := fun d => by ext; simp [mul_assoc]
      right_inv := fun d => by ext; simp [mul_assoc]
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  let ψ : MulAut (alternatingGroup (Fin 5)) := (eL.symm.trans φ).trans eL
  obtain ⟨σ, hσ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl
    (by omega)).2 ψ
  have hσψ : ∀ a : alternatingGroup (Fin 5), (ψ a : Equiv.Perm (Fin 5)) = σ * a * σ⁻¹ := by
    intro a
    rw [← hσ]
    exact (MulAut.conjNormal_apply σ a).symm
  let a : alternatingGroup (Fin 5) := eL ⟨u, hu⟩
  let c : alternatingGroup (Fin 5) := eL ⟨v, hv⟩
  have hψa : ψ a = a := by
    show eL (φ (eL.symm (eL ⟨u, hu⟩))) = eL ⟨u, hu⟩
    rw [MulEquiv.symm_apply_apply]
    congr 1
    ext
    show w * u * w⁻¹ = u
    rw [hwu]; group
  have hψc : ψ c = c := by
    show eL (φ (eL.symm (eL ⟨v, hv⟩))) = eL ⟨v, hv⟩
    rw [MulEquiv.symm_apply_apply]
    congr 1
    ext
    show w * v * w⁻¹ = v
    rw [hwv]; group
  have hσa : σ * (a : Equiv.Perm (Fin 5)) = a * σ := by
    have := hσψ a
    rw [hψa] at this
    have h2 : σ * (a : Equiv.Perm (Fin 5)) * σ⁻¹ * σ = (a : Equiv.Perm (Fin 5)) * σ := by
      rw [← this]
    simpa [mul_assoc] using h2
  have hσc : σ * (c : Equiv.Perm (Fin 5)) = c * σ := by
    have := hσψ c
    rw [hψc] at this
    have h2 : σ * (c : Equiv.Perm (Fin 5)) * σ⁻¹ * σ = (c : Equiv.Perm (Fin 5)) * σ := by
      rw [← this]
    simpa [mul_assoc] using h2
  have key : ∀ (τ : G) (hτ : τ ∈ L),
      σ = ((eL ⟨τ, hτ⟩ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) →
        ∀ l ∈ L, w * l * w⁻¹ = τ * l * τ⁻¹ := by
    intro τ hτ hστ l hl
    have h1 : ψ (eL ⟨l, hl⟩) = eL ⟨τ, hτ⟩ * eL ⟨l, hl⟩ * (eL ⟨τ, hτ⟩)⁻¹ := by
      apply Subtype.ext
      rw [hσψ, hστ]
      simp
    have h2 : ψ (eL ⟨l, hl⟩) = eL ⟨w * l * w⁻¹, hw l hl⟩ := by
      show eL (φ (eL.symm (eL ⟨l, hl⟩))) = _
      rw [MulEquiv.symm_apply_apply]
      rfl
    have h3 : eL ⟨w * l * w⁻¹, hw l hl⟩ = eL (⟨τ, hτ⟩ * ⟨l, hl⟩ * ⟨τ, hτ⟩⁻¹) := by
      rw [← h2, h1, map_mul, map_mul, map_inv]
    have h4 := congrArg Subtype.val (eL.injective h3)
    simpa using h4
  have hc1 : ((a : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) ≠ 1 := by
    intro h
    have : a = 1 := Subtype.ext h
    have := eL.injective (this.trans (map_one eL).symm)
    exact hu1 (congrArg Subtype.val this)
  have hc2 : ((c : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) ≠ 1 := by
    intro h
    have : c = 1 := Subtype.ext h
    have := eL.injective (this.trans (map_one eL).symm)
    exact hv1 (congrArg Subtype.val this)
  have hac1 : ((a : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) ≠ c := by
    intro h
    have := eL.injective (Subtype.ext h)
    exact huv (congrArg Subtype.val this)
  have ha2 : ((a : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) * a = 1 := by
    have : a * a = 1 := by
      show eL ⟨u, hu⟩ * eL ⟨u, hu⟩ = 1
      rw [← map_mul, ← map_one eL]
      congr 1
      ext; simpa using hu2
    simpa using congrArg Subtype.val this
  have hc22 : ((c : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) * c = 1 := by
    have : c * c = 1 := by
      show eL ⟨v, hv⟩ * eL ⟨v, hv⟩ = 1
      rw [← map_mul, ← map_one eL]
      congr 1
      ext; simpa using hv2
    simpa using congrArg Subtype.val this
  have hac : ((a : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) * c = c * a := by
    have : a * c = c * a := by
      show eL ⟨u, hu⟩ * eL ⟨v, hv⟩ = eL ⟨v, hv⟩ * eL ⟨u, hu⟩
      rw [← map_mul, ← map_mul]
      congr 1
      ext; simpa using hc
    simpa using congrArg Subtype.val this
  rcases s5CenV4 a c ha2 hc22 hc1 hc2 hac1 hac
      (Equiv.Perm.mem_alternatingGroup.mp a.2) (Equiv.Perm.mem_alternatingGroup.mp c.2)
      σ hσa hσc with h | h | h | h
  · refine ⟨1, by simp, key 1 L.one_mem ?_⟩
    have : eL ⟨1, L.one_mem⟩ = 1 := by
      rw [show (⟨1, L.one_mem⟩ : ↥L) = 1 from rfl, map_one]
    rw [h, this]
    rfl
  · exact ⟨u, by simp, key u hu h⟩
  · exact ⟨v, by simp, key v hv h⟩
  · refine ⟨u * v, by simp, key (u * v) (L.mul_mem hu hv) ?_⟩
    have : (⟨u * v, L.mul_mem hu hv⟩ : ↥L) = ⟨u, hu⟩ * ⟨v, hv⟩ := rfl
    rw [h, this, map_mul]
    rfl

theorem m42_mem_closure_inv_pair {u v : G} (hu2 : u * u = 1) (hv2 : v * v = 1)
    (hc : u * v = v * u) :
    ∀ y ∈ Subgroup.closure ({u, v} : Set G), y = 1 ∨ y = u ∨ y = v ∨ y = u * v := by
  have hvu : v * u = u * v := hc.symm
  have e1 : ∀ z, u * (u * z) = z := fun z => by rw [← mul_assoc, hu2, one_mul]
  have e2 : ∀ z, v * (v * z) = z := fun z => by rw [← mul_assoc, hv2, one_mul]
  have e4 : v * (u * v) = u := by rw [← hvu, e2]
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] <;>
      simp [mul_assoc, hu2, hv2, e1, e2, hvu, e4]
  | inv x _ hx =>
    have hi : (u * v)⁻¹ = u * v := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hu2, inv_eq_of_mul_eq_one_right hv2, hc]
    rcases hx with hx | hx | hx | hx <;> rw [hx]
    · simp
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hu2))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hv2)))
    · exact Or.inr (Or.inr (Or.inr hi))

theorem m42_U_cen_V [Finite G] {u v b : G} {V : Subgroup G} (hVp : IsPGroup 2 V)
    (hu : u ∈ V) (hv : v ∈ V) (hu2 : u * u = 1) (hv2 : v * v = 1) (hu1 : u ≠ 1)
    (hc : u * v = v * u) (hbu : b * u * b⁻¹ = v) (hbv : b * v * b⁻¹ = u * v)
    (hVn : ∀ x ∈ V, ∀ y ∈ Subgroup.closure ({u, v} : Set G),
      x * y * x⁻¹ ∈ Subgroup.closure ({u, v} : Set G))
    (hbV : ∀ x ∈ V, b⁻¹ * x * b ∈ V) :
    ∀ x ∈ V, ∀ y ∈ Subgroup.closure ({u, v} : Set G), x * y = y * x := by
  set U := Subgroup.closure ({u, v} : Set G) with hU
  have hUV : U ≤ V := by
    rw [hU, Subgroup.closure_le]
    rintro z (rfl | rfl)
    exacts [hu, hv]
  haveI : Group.IsNilpotent ↥V := hVp.isNilpotent
  let Ub : Subgroup ↥V := U.subgroupOf V
  haveI : Ub.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hVn g.1 g.2 n hn⟩
  have hUb : Ub ≠ ⊥ := by
    intro h
    have : (⟨u, hu⟩ : ↥V) ∈ Ub := Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure (by simp))
    rw [h, Subgroup.mem_bot] at this
    exact hu1 (congrArg Subtype.val this)
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hUb)
  have hzU : z.1 ∈ U := Subgroup.mem_subgroupOf.mp hz.1
  have hzc : ∀ x ∈ V, x * z.1 = z.1 * x := fun x hx => by
    have := Subgroup.mem_center_iff.mp hz.2 ⟨x, hx⟩
    exact congrArg Subtype.val this
  have hz1' : z.1 ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  have hconj : ∀ y : G, (∀ x ∈ V, x * y = y * x) →
      ∀ x ∈ V, x * (b * y * b⁻¹) = (b * y * b⁻¹) * x := by
    intro y hy x hx
    have h1 := hy _ (hbV x hx)
    calc x * (b * y * b⁻¹) = b * ((b⁻¹ * x * b) * y) * b⁻¹ := by group
      _ = b * (y * (b⁻¹ * x * b)) * b⁻¹ := by rw [h1]
      _ = (b * y * b⁻¹) * x := by group
  have hvu : v * u = u * v := hc.symm
  have hcu : ∀ x ∈ V, x * u = u * x ∧ x * v = v * x := by
    rcases m42_mem_closure_inv_pair hu2 hv2 hc _ hzU with h | h | h | h
    · exact absurd h hz1'
    · intro x hx
      have hu' : ∀ x ∈ V, x * u = u * x := fun x hx => h ▸ hzc x hx
      have hv' : ∀ x ∈ V, x * v = v * x := fun x hx => hbu ▸ hconj u hu' x hx
      exact ⟨hu' x hx, hv' x hx⟩
    · intro x hx
      have hv' : ∀ x ∈ V, x * v = v * x := fun x hx => h ▸ hzc x hx
      have huv' : ∀ x ∈ V, x * (u * v) = (u * v) * x := fun x hx => hbv ▸ hconj v hv' x hx
      have hu' : ∀ x ∈ V, x * u = u * x := by
        intro x hx
        have h2 := hconj (u * v) huv' x hx
        have e : b * (u * v) * b⁻¹ = u := by
          calc b * (u * v) * b⁻¹ = (b * u * b⁻¹) * (b * v * b⁻¹) := by group
            _ = v * (u * v) := by rw [hbu, hbv]
            _ = u := by rw [← hvu, ← mul_assoc, hv2, one_mul]
        rwa [e] at h2
      exact ⟨hu' x hx, hv' x hx⟩
    · intro x hx
      have huv' : ∀ x ∈ V, x * (u * v) = (u * v) * x := fun x hx => h ▸ hzc x hx
      have hu' : ∀ x ∈ V, x * u = u * x := by
        intro x hx
        have h2 := hconj (u * v) huv' x hx
        have e : b * (u * v) * b⁻¹ = u := by
          calc b * (u * v) * b⁻¹ = (b * u * b⁻¹) * (b * v * b⁻¹) := by group
            _ = v * (u * v) := by rw [hbu, hbv]
            _ = u := by rw [← hvu, ← mul_assoc, hv2, one_mul]
        rwa [e] at h2
      have hv' : ∀ x ∈ V, x * v = v * x := fun x hx => hbu ▸ hconj u hu' x hx
      exact ⟨hu' x hx, hv' x hx⟩
  intro x hx y hy
  have : U ≤ Subgroup.centralizer {x} := by
    rw [hU, Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcu x hx).1.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcu x hx).2.symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (this hy)).symm

end CFSG.RankThree.PartTwo.Sec21.FF79
