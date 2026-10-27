module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUSigned
import CFSG.LocalAnalysis.StandardType.GGStdPosC24HypSU
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCentral

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Open

theorem ggTorusSignedEltSC_of_centralQuotient {p : ℕ} (hp : p.Prime) {G R : Type}
    [Group G] [Finite G] [Group R] (q : G →* R) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center G) (hcp : ¬ p ∣ Nat.card (Subgroup.center G))
    (h : GGTorusSignedEltSC p G) : GGTorusSignedEltSC p R := by
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
  obtain ⟨k, τG, hτGinj, hτGrange, hS, hP, hN⟩ :=
    h Et hEt_ab (by rw [hcard]; exact h3) hscEt
  have hτGEt : ∀ f, τG f ∈ Et := fun f => hτGrange ▸ ⟨f, rfl⟩
  let τ : (Fin k → Multiplicative (ZMod p)) →* R := q.comp τG
  have hτinj : Function.Injective τ := fun x y hxy =>
    hτGinj (eq_of_lift_pow_eq_one hp hker hcp hxy (hτGEt x).1 (hτGEt y).1)
  have hτrange : τ.range = E := by
    change (q.comp τG).range = E
    rw [MonoidHom.range_comp, hτGrange]
    exact hmap
  have hmove : ∀ F : (Fin k → Multiplicative (ZMod p)) → Fin k → Multiplicative (ZMod p),
      (∃ w : G, ∀ f, w * τG f * w⁻¹ = τG (F f)) → ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (F f) := by
    rintro F ⟨w, hw⟩
    refine ⟨q w, fun f => ?_⟩
    change q w * q (τG f) * (q w)⁻¹ = q (τG (F f))
    rw [← hw, map_mul, map_mul, map_inv]
  refine ⟨k, τ, hτinj, hτrange, fun i => hmove _ (hS i), fun σ => hmove _ (hP σ), ?_⟩
  intro g hg
  obtain ⟨g', rfl⟩ := hq g
  have hg' : ∀ e ∈ Et, g' * e * g'⁻¹ ∈ Et := by
    intro e he
    refine ⟨by rw [conj_pow, he.1, mul_one, mul_inv_cancel], ?_⟩
    rw [map_mul, map_mul, map_inv]
    exact hg _ he.2
  obtain ⟨π, ε, hε, hrel⟩ := hN g' hg'
  refine ⟨π, ε, hε, fun f f' hff => hrel f f' ?_⟩
  refine eq_of_lift_pow_eq_one hp hker hcp ?_ (hg' _ (hτGEt f)).1 (hτGEt f').1
  rw [map_mul, map_mul, map_inv]
  exact hff

theorem ggTorusSignedEltSC_statedProj_hyp {n p : ℕ} {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData 2 n F) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1) :
    GGTorusSignedEltSC p (StatedProj (StatedSU 6 (2 ^ n) F)) := by
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 3) (ε := 0) h
  have hSU : GGTorusSignedEltSC p (StatedSU 6 (2 ^ n) F) :=
    ggTorusSignedEltSC_of_mulEquiv (hypTransport h hR).symm
      (ggTorusSignedEltSC_hypSU_three h hp hp2 hpq)
  refine ggTorusSignedEltSC_of_centralQuotient hp
    (QuotientGroup.mk' ((StatedScalars (Fin 6) F).subgroupOf (StatedSU 6 (2 ^ n) F)))
    (QuotientGroup.mk'_surjective _) ?_ ?_ hSU
  · rw [QuotientGroup.ker_mk']
    exact scalars_le_center_statedSU
  ·
    intro hdvd
    have h1 := hdvd.trans (card_center_statedSU_dvd h.card_eq_sq (by norm_num))
    have hsub : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by
      have : 0 < 2 ^ n := Nat.two_pow_pos n
      omega
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hsub ▸ Nat.dvd_sub h1 hpq))

end CFSG.StandardType

end
