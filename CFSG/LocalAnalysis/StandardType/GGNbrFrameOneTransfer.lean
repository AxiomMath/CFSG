module

public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneCoord
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneCoordModel
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneEltDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameNineTransfer
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUSigned

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB Multiplicative NbrFrameOne

theorem ggTorusFrame_of_frameEltSC {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hp2 : p ≠ 2) (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R) (h : GGTorusFrameEltSC p R) :
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
      GGTorusTBGroup p r R I L' ψ A → GGTorusFrame p A := by
  intro L' _ _ ψ A hA
  obtain ⟨k, τ, Θ, -, ⟨i, j, hij, ⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩⟩, hmodel⟩ :=
    ggTorusCoordModel hp hp2 hZ hIp hcp
      (fun k τ => ∃ i j : Fin k, i ≠ j ∧
        (∃ w : R, ∀ t : Fin k → ZMod p,
          w⁻¹ * τ (ofAdd t) * w = τ (ofAdd (Function.update t i (-t i)))) ∧
        ∃ w : R, ∀ t : Fin k → ZMod p, w⁻¹ * τ (ofAdd t) * w = τ (ofAdd (t ∘ Equiv.swap i j)))
      h L' ψ A hA
  obtain ⟨n₁, hn₁, hW₁, heq₁⟩ := hmodel (negAut i) w₁ fun f => by
    rw [← ofAdd_toAdd f, hw₁ (toAdd f), negAut_apply i (toAdd f)]
  obtain ⟨n₂, hn₂, hW₂, heq₂⟩ := hmodel (swapAut i j) w₂ fun f => by
    rw [← ofAdd_toAdd f, hw₂ (toAdd f), swapAut_apply i j (toAdd f)]
  have hrefl₁ : GGIsReflection p (ggConjAut A hn₁) := by
    rw [heq₁]
    exact ggIsReflection_congr Θ (negAut_sq i) (card_fix_negAut hp hp2 i)
  have hrefl₂ : GGIsReflection p (ggConjAut A hn₂) := by
    rw [heq₂]
    exact ggIsReflection_congr Θ (swapAut_sq i j) (card_fix_swapAut hp hij)
  refine ⟨ggConjAut A hn₁, ⟨n₁, hn₁, hW₁, rfl, hrefl₁⟩, ggConjAut A hn₂,
    ⟨n₂, hn₂, hW₂, rfl, hrefl₂⟩, ?_⟩
  rw [heq₁, heq₂, ← map_mul, MulEquiv.orderOf_eq, orderOf_negAut_mul_swapAut hp hp2 hij]

theorem ggTorusFrameEltSC_of_mulEquiv {p : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') (h : GGTorusFrameEltSC p R') : GGTorusFrameEltSC p R := by
  intro E hE h3 hsc
  have hE' : IsElemAbelian p (E.map e.toMonoidHom) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha', ha'e⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨b', hb', hb'e⟩ := Subgroup.mem_map.mp b.2
      show (↑a : R') * ↑b = ↑b * ↑a
      rw [← ha'e, ← hb'e, ← map_mul, ← map_mul, TableB.IsElemAbelian.comm hE ha' hb']
    · obtain ⟨x', hx', hx'e⟩ := Subgroup.mem_map.mp hx
      rw [← hx'e, ← map_pow, hE.2 x' hx', map_one]
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (K := E) e.injective
  have hsc' : ∀ g : R', (∀ x ∈ E.map e.toMonoidHom, g * x = x * g) → g ^ p = 1 →
      g ∈ E.map e.toMonoidHom := by
    intro g hg hgp
    have hg₀ : e.symm g ∈ E := by
      refine hsc (e.symm g) (fun x hx => ?_) (by rw [← map_pow, hgp, map_one])
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hg (e x) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    exact Subgroup.mem_map.mpr ⟨e.symm g, hg₀, by simp⟩
  obtain ⟨k, τ', hτ'inj, hτ'range, i, j, hij, ⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩⟩ :=
    h (E.map e.toMonoidHom) hE' (by rw [hcard]; exact h3) hsc'
  let τ : Multiplicative (Fin k → ZMod p) →* R := e.symm.toMonoidHom.comp τ'
  have hτinj : Function.Injective τ := e.symm.injective.comp hτ'inj
  have hτrange : τ.range = E := by
    change (e.symm.toMonoidHom.comp τ').range = E
    rw [MonoidHom.range_comp, hτ'range, Subgroup.map_map]
    have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id R := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
  refine ⟨k, τ, hτinj, hτrange, i, j, hij, ⟨e.symm w₁, ?_⟩, ⟨e.symm w₂, ?_⟩⟩
  · intro t
    calc (e.symm w₁)⁻¹ * τ (ofAdd t) * e.symm w₁
        = e.symm (w₁⁻¹ * τ' (ofAdd t) * w₁) := by
          simp only [τ, MonoidHom.comp_apply, map_mul, map_inv]
          rfl
      _ = e.symm (τ' (negAut i (ofAdd t))) := by rw [hw₁ t, negAut_apply]
      _ = τ (negAut i (ofAdd t)) := rfl
  · intro t
    calc (e.symm w₂)⁻¹ * τ (ofAdd t) * e.symm w₂
        = e.symm (w₂⁻¹ * τ' (ofAdd t) * w₂) := by
          simp only [τ, MonoidHom.comp_apply, map_mul, map_inv]
          rfl
      _ = e.symm (τ' (swapAut i j (ofAdd t))) := by rw [hw₂ t, swapAut_apply]
      _ = τ (swapAut i j (ofAdd t)) := rfl

theorem ggTorusFrameEltSC_of_centralQuotient {p : ℕ} (hp : p.Prime) {G R : Type} [Group G]
    [Finite G] [Group R] (q : G →* R) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center G) (hcp : ¬ p ∣ Nat.card (Subgroup.center G))
    (h : GGTorusFrameEltSC p G) : GGTorusFrameEltSC p R := by
  intro E hE h3 hsc
  let Et : Subgroup G :=
    { carrier := {g | g ^ p = 1 ∧ q g ∈ E}
      one_mem' := ⟨one_pow p, by rw [map_one]; exact E.one_mem⟩
      mul_mem' := by
        intro x y hx hy
        have hxy : Commute x y :=
          commute_of_lift_pow_eq_one hp hker hcp
            (TableB.IsElemAbelian.comm hE hx.2 hy.2) hy.1
        exact ⟨by rw [hxy.mul_pow, hx.1, hy.1, one_mul],
          by rw [map_mul]; exact E.mul_mem hx.2 hy.2⟩
      inv_mem' := by
        intro x hx
        exact ⟨by rw [inv_pow, hx.1, inv_one], by rw [map_inv]; exact E.inv_mem hx.2⟩ }
  have hEt_ab : IsElemAbelian p Et := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hx.1⟩
    exact commute_of_lift_pow_eq_one hp hker hcp
      (TableB.IsElemAbelian.comm hE a.2.2 b.2.2) b.2.1
  have hcard : Nat.card Et = Nat.card E := by
    refine Nat.card_congr (Equiv.ofBijective (fun x : Et => (⟨q x, x.2.2⟩ : E)) ⟨?_, ?_⟩)
    · intro x y hxy
      exact Subtype.ext
        (eq_of_lift_pow_eq_one hp hker hcp (Subtype.ext_iff.mp hxy) x.2.1 y.2.1)
    · intro e
      obtain ⟨x, hxq, hxp⟩ := exists_lift_pow_eq_one hp hq hker hcp (hE.2 e e.2)
      exact ⟨⟨x, hxp, hxq ▸ e.2⟩, Subtype.ext hxq⟩
  have hscEt : ∀ g : G, (∀ e ∈ Et, g * e = e * g) → g ^ p = 1 → g ∈ Et := by
    intro g hg hgp
    refine ⟨hgp, ?_⟩
    refine hsc (q g) (fun e he => ?_) (by rw [← map_pow, hgp, map_one])
    obtain ⟨x, hxq, hxp⟩ := exists_lift_pow_eq_one hp hq hker hcp (hE.2 e he)
    have hxEt : x ∈ Et := ⟨hxp, hxq ▸ he⟩
    have h1 : q (g * x) = q (x * g) := congrArg q (hg x hxEt)
    rwa [map_mul, map_mul, hxq] at h1
  have hmap : Et.map q = E := by
    refine le_antisymm ?_ ?_
    · intro e he
      obtain ⟨x, hxEt, rfl⟩ := Subgroup.mem_map.mp he
      exact hxEt.2
    · intro e he
      obtain ⟨x, hxq, hxp⟩ := exists_lift_pow_eq_one hp hq hker hcp (hE.2 e he)
      exact Subgroup.mem_map.mpr ⟨x, ⟨hxp, hxq ▸ he⟩, hxq⟩
  obtain ⟨k, τG, hτGinj, hτGrange, i, j, hij, ⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩⟩ :=
    h Et hEt_ab (by rw [hcard]; exact h3) hscEt
  let τ : Multiplicative (Fin k → ZMod p) →* R := q.comp τG
  have hτinj : Function.Injective τ := by
    intro x y hxy
    have hxEt : τG x ∈ Et := hτGrange ▸ ⟨x, rfl⟩
    have hyEt : τG y ∈ Et := hτGrange ▸ ⟨y, rfl⟩
    exact hτGinj (eq_of_lift_pow_eq_one hp hker hcp hxy hxEt.1 hyEt.1)
  have hτrange : τ.range = E := by
    change (q.comp τG).range = E
    rw [MonoidHom.range_comp, hτGrange]
    exact hmap
  refine ⟨k, τ, hτinj, hτrange, i, j, hij, ⟨q w₁, ?_⟩, ⟨q w₂, ?_⟩⟩
  · intro t
    calc (q w₁)⁻¹ * τ (ofAdd t) * q w₁
        = q (w₁⁻¹ * τG (ofAdd t) * w₁) := by
          simp only [τ, MonoidHom.comp_apply, map_mul, map_inv]
      _ = q (τG (negAut i (ofAdd t))) := by rw [hw₁ t, negAut_apply]
      _ = τ (negAut i (ofAdd t)) := rfl
  · intro t
    calc (q w₂)⁻¹ * τ (ofAdd t) * q w₂
        = q (w₂⁻¹ * τG (ofAdd t) * w₂) := by
          simp only [τ, MonoidHom.comp_apply, map_mul, map_inv]
      _ = q (τG (swapAut i j (ofAdd t))) := by rw [hw₂ t, swapAut_apply]
      _ = τ (swapAut i j (ofAdd t)) := rfl

theorem ggTorusFrameEltSC_of_signedEltSC {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    (h : GGTorusSignedEltSC p R) : GGTorusFrameEltSC p R := by
  intro E hE h3 hsc
  obtain ⟨k, τ, hτinj, hτE, hsgn, hperm, -⟩ := h E hE h3 hsc
  have hk : 3 ≤ k := by
    have hcV : Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
      rw [Nat.card_fun, Nat.card_fin]
      congr 1
      exact Nat.card_zmod p
    have h1 : Nat.card (Fin k → Multiplicative (ZMod p)) = Nat.card E := by
      rw [← hτE]
      refine Nat.card_congr (Equiv.ofBijective τ.rangeRestrict ⟨?_, ?_⟩)
      · intro x y hxy
        exact hτinj (congrArg Subtype.val hxy)
      · intro y
        obtain ⟨x, hx⟩ := y.2
        exact ⟨x, Subtype.ext hx⟩
    rw [hcV] at h1
    rw [← h1] at h3
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h3
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    simp [i, j] at this
  let e := MulEquiv.funMultiplicative (Fin k) (ZMod p)
  let τ' : Multiplicative (Fin k → ZMod p) →* R := τ.comp e.toMonoidHom
  have hτ'inj : Function.Injective τ' := hτinj.comp e.injective
  have hτ'range : τ'.range = E := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      rw [← hτE]
      exact ⟨e x, rfl⟩
    · intro y hy
      have hy' : y ∈ τ.range := hτE ▸ hy
      obtain ⟨z, rfl⟩ := hy'
      refine ⟨e.symm z, ?_⟩
      show τ (e (e.symm z)) = τ z
      rw [MulEquiv.apply_symm_apply]
  obtain ⟨w₁, hw₁⟩ := hsgn i
  obtain ⟨w₂, hw₂⟩ := hperm (Equiv.swap i j)
  refine ⟨k, τ', hτ'inj, hτ'range, i, j, hij, ⟨w₁⁻¹, ?_⟩, ⟨w₂⁻¹, ?_⟩⟩
  · intro t
    have hcoord : SpCoord.sgnAut i (e (ofAdd t)) = e (negAut i (ofAdd t)) := by
      funext l
      rw [SpCoord.sgnAut_apply, negAut_apply]
      by_cases hl : l = i
      · subst hl
        simp [e]
      · simp [e, Function.update_of_ne hl]
    calc w₁⁻¹⁻¹ * τ' (ofAdd t) * w₁⁻¹
        = w₁ * τ (e (ofAdd t)) * w₁⁻¹ := by
          rw [inv_inv]
          rfl
      _ = τ (SpCoord.sgnAut i (e (ofAdd t))) := hw₁ (e (ofAdd t))
      _ = τ (e (negAut i (ofAdd t))) := by rw [hcoord]
      _ = τ' (negAut i (ofAdd t)) := rfl
  · intro t
    have hcoord : SpCoord.permAut (Equiv.swap i j) (e (ofAdd t)) =
        e (swapAut i j (ofAdd t)) := by
      funext l
      rw [SpCoord.permAut_apply, swapAut_apply]
      simp [e, Equiv.swap_inv]
    calc w₂⁻¹⁻¹ * τ' (ofAdd t) * w₂⁻¹
        = w₂ * τ (e (ofAdd t)) * w₂⁻¹ := by
          rw [inv_inv]
          rfl
      _ = τ (SpCoord.permAut (Equiv.swap i j) (e (ofAdd t))) := hw₂ (e (ofAdd t))
      _ = τ (e (swapAut i j (ofAdd t))) := by rw [hcoord]
      _ = τ' (swapAut i j (ofAdd t)) := rfl

end CFSG.StandardType

end
