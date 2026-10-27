module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PSUModelCore
public import CFSG.RankThree.GF2n.Stroth78.Sec4PSUModel

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
open CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)
open CFSG.Open (IsElemAbelian pCoreOf)

theorem exists_rigid_core_of_mulEquiv_U2 {m : ℕ} {Y : Type} [Group Y] (φ : Y ≃* U2 m)
    (hm : 5 ≤ m) {d : Y} (hd : φ d ∈ DU m) :
    ∃ W : Subgroup Y,
      W ≤ ⁅⁅Subgroup.centralizer {d}, Subgroup.centralizer {d}⁆,
        ⁅Subgroup.centralizer {d}, Subgroup.centralizer {d}⁆⁆ ∧
      CFSG.GroupTheory.oddOrderClosure W = W ∧
      ∀ A : Subgroup (MulAut Y), (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a * a = 1) →
        (∀ a ∈ A, a d = d) → MulAut.conj d ∈ A →
        (∀ x ∈ W, ∀ a ∈ A, MulAut.conj x * a * (MulAut.conj x)⁻¹ ∈ A) →
        ∀ a ∈ A, a = 1 ∨ a = MulAut.conj d := by
  obtain ⟨v, hv0, hv, hvd⟩ := mem_DU_iff.1 hd
  obtain ⟨W₀, k1, k2, k3, k4, k5⟩ := exists_core_centralizer_tqU hm hv0 hv
  have hφd : φ.symm (tqU v) = d := by rw [hvd, MulEquiv.symm_apply_apply]
  have hU1 : tqU v * tqU v = 1 := by rw [tqU_eq, ← map_mul, tq_mul_self hv, map_one]
  have hU2 : tqU v ≠ 1 := by
    rw [tqU_eq]
    intro h
    exact tq_ne_one (by omega) hv0 hv ((u2Equiv m).symm.injective (by rw [h, map_one]))
  have hkerφ : ∀ x ∈ (φ.symm.toMonoidHom).ker, x = 1 := by
    intro x hx
    have hx' : φ.symm x = 1 := hx
    exact φ.symm.injective (by rw [hx', map_one])
  have key := Sec4PSU.map_coreProperties φ.symm.toMonoidHom φ.symm.surjective
    (fun x hx => by rw [hkerφ x hx]; exact one_mem _)
    (fun x hx => by rw [hkerφ x hx, orderOf_one]; exact odd_one)
    hU1 hU2 k1 k2 k3 k4 k5
  simp only [MulEquiv.coe_toMonoidHom, hφd] at key
  obtain ⟨h1, h2, h3, h4, h5⟩ := key
  set W := W₀.map φ.symm.toMonoidHom with hW
  have hroot : CFSG.RankThree.GF2n.Tim79a.RootS2Model Y (Subgroup.zpowers d) := by
    have := CFSG.RankThree.GF2n.Tim79a.rootS2Model_map_of_bijective φ.symm.toMonoidHom
      φ.symm.bijective (rootS2Model_U2 (by omega) hv0 hv)
    rwa [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, hφd] at this
  refine ⟨W, h1, h2, fun A hcomm hsq hfix hcd hnorm a ha => ?_⟩
  have hcenter : Subgroup.center Y = ⊥ := by
    have hU := center_U2 (m := m) (by omega)
    rw [eq_bot_iff] at hU ⊢
    intro y hy
    have : φ y ∈ Subgroup.center (U2 m) := by
      rw [Subgroup.mem_center_iff] at hy ⊢
      intro g
      have := hy (φ.symm g)
      apply φ.symm.injective
      simpa [map_mul] using this
    have := hU this
    rw [Subgroup.mem_bot] at this ⊢
    exact φ.injective (by rw [this, map_one])
  have hκinj : Function.Injective (MulAut.conj : Y →* MulAut Y) := by
    intro x y hxy
    have hc : y⁻¹ * x ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun f : MulAut Y => f g) hxy
      simp only [MulAut.conj_apply] at this
      calc g * (y⁻¹ * x) = y⁻¹ * (y * g * y⁻¹) * x := by group
        _ = y⁻¹ * (x * g * x⁻¹) * x := by rw [this]
        _ = y⁻¹ * x * g := by group
    rw [hcenter, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.1 hc).symm
  have hconjconj : ∀ (f : MulAut Y) (y : Y), f * MulAut.conj y * f⁻¹ = MulAut.conj (f y) := by
    intro f y
    ext g
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
  have hdd : d * d = 1 := by
    apply φ.injective
    rw [map_mul, ← hvd, hU1, map_one]
  have hd1 : d ≠ 1 := fun h => hU2 (by rw [hvd, h, map_one])
  set E := A.comap (MulAut.conj : Y →* MulAut Y) with hE
  have hEel : IsElemAbelian 2 E := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hκinj ?_)⟩⟩, fun y hy => hκinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact hcomm _ x.2 _ y.2
    · rw [map_pow, map_one, sq]
      exact hsq _ hy
  have hzE : Subgroup.zpowers d ≤ E := (Subgroup.zpowers_le).2 hcd
  have hEC : E ≤ Subgroup.centralizer {d} := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hfix _ hy
    simp only [MulAut.conj_apply] at this
    calc y * d = y * d * y⁻¹ * y := by group
      _ = d * y := by rw [this]
  have hWE : ∀ x ∈ W, ∀ e ∈ E, x * e * x⁻¹ ∈ E := by
    intro x hx e he
    change MulAut.conj (x * e * x⁻¹) ∈ A
    rw [map_mul, map_mul, map_inv]
    exact hnorm x hx _ he
  have hEeq := h4 E hEel hzE hEC hWE
  have hle : ∀ K : Subgroup Y, ⁅K, K⁆ ≤ K := fun K =>
    Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hWC : W ≤ Subgroup.centralizer {d} := h1.trans ((hle _).trans (hle _))
  have hcomm' : ∀ x ∈ W, ∀ f ∈ A, x * (f x)⁻¹ ∈ Subgroup.zpowers d := by
    intro x hx f hf
    rw [← hEeq]
    change MulAut.conj (x * (f x)⁻¹) ∈ A
    have h1' := mul_mem (hnorm x hx f hf) (inv_mem hf)
    have e : MulAut.conj x * f * (MulAut.conj x)⁻¹ * f⁻¹ = MulAut.conj (x * (f x)⁻¹) := by
      have e1 : MulAut.conj x * f * (MulAut.conj x)⁻¹ * f⁻¹ =
          MulAut.conj x * (f * MulAut.conj x⁻¹ * f⁻¹) := by
        rw [map_inv]
        group
      rw [e1, hconjconj, map_inv f x, ← map_mul]
    rwa [e] at h1'
  have hfixA : ∀ b ∈ Subgroup.zpowers d, a b = b := by
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [map_zpow, hfix a ha]
  have hO₂ : ∀ b ∈ pCoreOf 2 (Subgroup.normalizer (Subgroup.zpowers d : Set Y)),
      b⁻¹ * a b ∈ Subgroup.zpowers d := by
    intro b hb
    have hbW := h3 hb
    have hu := hcomm' b hbW a ha
    set u := b * (a b)⁻¹ with hudef
    have hab : a b = u⁻¹ * b := by rw [hudef]; group
    have hbu : b⁻¹ * u⁻¹ * b = u⁻¹ := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hu
      have hbd := Subgroup.mem_centralizer_singleton_iff.1 (hWC hbW)
      have hcomm_bu : b * u⁻¹ = u⁻¹ * b := by
        rw [← hk, ← zpow_neg]
        exact (Commute.zpow_right (show Commute b d from hbd) (-k)).eq
      calc b⁻¹ * u⁻¹ * b = b⁻¹ * (u⁻¹ * b) := by group
        _ = b⁻¹ * (b * u⁻¹) := by rw [hcomm_bu]
        _ = u⁻¹ := by group
    rw [hab, ← mul_assoc, hbu]
    exact inv_mem hu
  obtain ⟨s, hs, has⟩ := hroot a hfixA hO₂
  have hsA : s ∈ Subgroup.zpowers d := by
    refine h5 s hs fun x hx => ?_
    have hxinv : x⁻¹ ∈ W := inv_mem hx
    have hu := hcomm' x⁻¹ hxinv a⁻¹ (inv_mem ha)
    have hai : a⁻¹ x⁻¹ = s⁻¹ * x⁻¹ * s := by
      rw [has, ← map_inv, MulAut.conj_apply, inv_inv]
    rw [hai] at hu
    have e : x⁻¹ * (s⁻¹ * x⁻¹ * s)⁻¹ = x⁻¹ * s⁻¹ * x * s := by group
    rwa [e] at hu
  rcases (Sec4PSU.mem_zpowers_iff_of_mul_self hdd hd1).1 hsA with h | h
  · left
    rw [has, h, map_one]
  · right
    rw [has, h]

end CFSG.RankThree.GF2n.Stroth78
