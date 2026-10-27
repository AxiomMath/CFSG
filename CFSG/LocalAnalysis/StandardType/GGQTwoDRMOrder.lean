module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMBar
public import CFSG.LocalAnalysis.StandardType.GGQTwoGlobLin

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Growth

theorem qTwoDRM_six_le_pow {d : ℕ} (hd : 3 ≤ d) : 6 * d ≤ 3 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih =>
    calc 6 * (d + 1) ≤ 3 * (6 * d) := by omega
      _ ≤ 3 * 3 ^ d := Nat.mul_le_mul_left 3 ih
      _ = 3 ^ (d + 1) := by rw [pow_succ]; ring

theorem qTwoDRM_growth {d : ℕ} (hd : 7 ≤ d) :
    8 * (3 ^ d * (2 ^ (d - 1) * (d - 1).factorial)) < 3 ^ (d * (d - 1) / 2) := by
  induction d, hd using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ d hd ih =>
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    rw [Nat.triangle_succ]
    have h1 : 8 * (3 ^ (k + 1 + 1) * (2 ^ (k + 1 + 1 - 1) * (k + 1 + 1 - 1).factorial)) =
        (8 * (3 ^ (k + 1) * (2 ^ (k + 1 - 1) * (k + 1 - 1).factorial))) * (6 * (k + 1)) := by
      simp only [Nat.add_sub_cancel]
      rw [Nat.factorial_succ, pow_succ, pow_succ 2 k]
      ring
    rw [h1]
    have h2 : 8 * (3 ^ (k + 1) * (2 ^ (k + 1 - 1) * (k + 1 - 1).factorial)) * (6 * (k + 1)) <
        3 ^ ((k + 1) * (k + 1 - 1) / 2) * (6 * (k + 1)) :=
      Nat.mul_lt_mul_of_pos_right ih (by positivity)
    have h3 : 3 ^ ((k + 1) * (k + 1 - 1) / 2) * (6 * (k + 1)) ≤
        3 ^ ((k + 1) * (k + 1 - 1) / 2) * 3 ^ (k + 1) :=
      Nat.mul_le_mul_left _ (qTwoDRM_six_le_pow (d := k + 1) (by omega))
    calc _ < _ := h2
      _ ≤ _ := h3
      _ = _ := (pow_add _ _ _).symm

end Growth

section Action

variable {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G} {x : G}
  {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Additive ↥Bs ≃+ V}
  {U : Submodule (ZMod 3) V} {Abar : Subgroup (↥U ≃ₗ[ZMod 3] ↥U)}
  {ρ : ↥(ggAInf 3 B Bs x L D J) ≃* ↥Abar}

theorem qTwoDRM_actionCard_le (hx : x ∈ Bs) {S : ℕ}
    (hS : Nat.card {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a ⟨x, hx⟩ = ⟨x, hx⟩} ≤ S)
    (hD : GGSecFiveBarData 3 B Bs x L D J ι U Abar ρ) :
    Nat.card Abar ≤ 3 ^ Module.finrank (ZMod 3) U * S := by
  classical
  have : Fact (Nat.Prime 3) := Nat.fact_prime_three
  let A : Type := ↥(ggAInf 3 B Bs x L D J)
  let b0 : ↥Bs := ⟨x, hx⟩
  let : MulAction A ↥Bs :=
    MulAction.compHom ↥Bs (Subgroup.subtype (ggAInf 3 B Bs x L D J))
  have hfinV : Finite V := Finite.of_injective (⇑ι.symm) ι.symm.injective
  have hfinU : Finite ↥U := Subtype.finite
  have hfinUmod : Module.Finite (ZMod 3) ↥U := Module.Finite.of_finite
  have hfinBs : Fintype ↥Bs := Fintype.ofFinite ↥Bs
  have hfinMulAut : Fintype (MulAut ↥Bs) :=
    Fintype.ofInjective (fun e : MulAut ↥Bs => (e : ↥Bs → ↥Bs))
      (fun a b h => MulEquiv.ext (fun y => congrArg (fun f : ↥Bs → ↥Bs => f y) h))
  have hfinA : Fintype A := Fintype.ofFinite A
  have hfinOrb : Fintype (MulAction.orbit A b0) := Fintype.ofFinite _
  have hfinStab : Fintype (MulAction.stabilizer A b0) := Fintype.ofFinite _
  have hcardU : Nat.card ↥U = 3 ^ Module.finrank (ZMod 3) U := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 3) (V := ↥U), Nat.card_zmod]
  have hOS :
      Nat.card (MulAction.orbit A b0) * Nat.card (MulAction.stabilizer A b0) = Nat.card A := by
    rw [Nat.card_eq_fintype_card (α := MulAction.orbit A b0),
      Nat.card_eq_fintype_card (α := MulAction.stabilizer A b0),
      Nat.card_eq_fintype_card (α := A)]
    exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group A b0
  have horbit : Nat.card (MulAction.orbit A b0) ≤ Nat.card ↥U := by
    let f : MulAction.orbit A b0 → ↥U := fun y =>
      ⟨ι y.1 - ι (Additive.ofMul b0), by
        obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp y.2
        have hdiff :
            ι y.1 - ι (Additive.ofMul b0) =
              ggLin (p := 3) ι (a : MulAut ↥Bs) (ι (Additive.ofMul b0)) -
                ι (Additive.ofMul b0) := by
          rw [← ha, ggLin_apply_ofMul]
          rfl
        rw [hdiff]
        exact hD.2.2.2.2.1 (a : MulAut ↥Bs) a.2 (ι (Additive.ofMul b0))⟩
    refine Nat.card_le_card_of_injective f ?_
    intro y1 y2 h
    have hz : ι y1.1 - ι (Additive.ofMul b0) =
        ι y2.1 - ι (Additive.ofMul b0) := congrArg Subtype.val h
    have hz' : ι y1.1 = ι y2.1 := by
      have := congrArg (fun z : V => z + ι (Additive.ofMul b0)) hz
      simpa using this
    exact Subtype.ext (ι.injective hz')
  have hstab : Nat.card (MulAction.stabilizer A b0) ≤
      Nat.card {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a b0 = b0} := by
    let f : MulAction.stabilizer A b0 →
        {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a b0 = b0} := fun s =>
      ⟨(s.1 : MulAut ↥Bs), qTwoGlobBnd_ainf_le_induced B Bs L D J x s.1.2, s.2⟩
    refine Nat.card_le_card_of_injective f ?_
    intro s t h
    have h1 : (s.1 : MulAut ↥Bs) = (t.1 : MulAut ↥Bs) :=
      congrArg (fun z : {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a b0 = b0} =>
        (z : MulAut ↥Bs)) h
    exact Subtype.ext (Subtype.ext h1)
  have hA : Nat.card A ≤ 3 ^ Module.finrank (ZMod 3) U * S := by
    rw [← hOS]
    exact Nat.mul_le_mul (hcardU ▸ horbit) (le_trans hstab hS)
  have hcard : Nat.card Abar = Nat.card A := (Nat.card_congr ρ.toEquiv).symm
  exact hcard ▸ hA

end Action

section Dispatch

variable {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G} {x : G}
  {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Additive ↥Bs ≃+ V}
  {U : Submodule (ZMod 3) V} {Abar : Subgroup (↥U ≃ₗ[ZMod 3] ↥U)}
  {ρ : ↥(ggAInf 3 B Bs x L D J) ≃* ↥Abar}

theorem qTwoD_family_linWeyl {m : ℕ} (hm : 5 ≤ m)
    (hfin : Module.finrank (ZMod 3) U = m)
    (hD : GGSecFiveBarData 3 B Bs x L D J ι U Abar ρ)
    (hcard : 8 * Nat.card Abar < 3 ^ (m * (m - 1) / 2))
    (hFam : ZS.Family 3 Abar) : ZS.LinWeyl 3 Abar := by
  let : Finite V := qTwoGlobLin_finite (ι := ι)
  let : Module.Finite (ZMod 3) U := Module.Finite.of_finite
  have hd4 : 4 ≤ Module.finrank (ZMod 3) U := by omega
  cases hFam with
  | weyl hW => exact hW
  | slpm hSL =>
    exfalso
    have hlower := ZS.pow_le_card_of_sl_le hfin Abar (fun g hg => (hSL g).mpr (Or.inl hg))
    have : 3 ^ (m * (m - 1) / 2) < 3 ^ (m * (m - 1) / 2) :=
      lt_of_le_of_lt (hlower.trans (Nat.le_mul_of_pos_left _ (by norm_num))) hcard
    exact lt_irrefl _ this
  | orth Q hQ hO =>
    exfalso
    have hcomm := qTwoGlobLin_orth_commutators (ι := ι) Q hQ (Or.inl hO) (by omega)
    have hlower := ZS.pow_le_card_of_commutator_isometry_mem (p := 3) (by decide) hfin
      (by omega) hQ Abar hcomm
    exact absurd (lt_of_le_of_lt hlower hcard) (lt_irrefl _)
  | orthClass Q c hQ hc hO =>
    exfalso
    have hcomm := qTwoGlobLin_orth_commutators (ι := ι) Q hQ (Or.inr ⟨c, hc, hO⟩) (by omega)
    have hlower := ZS.pow_le_card_of_commutator_isometry_mem (p := 3) (by decide) hfin
      (by omega) hQ Abar hcomm
    exact absurd (lt_of_le_of_lt hlower hcard) (lt_irrefl _)
  | gmmn f i₀ i₁ ζ t hi ht hζ hO =>
    exact False.elim (qTwo_family_imprimitive_excl f i₀ i₁ ζ t hi (Or.inl ⟨ht, hζ, hO⟩))
  | g2mmn f i₀ i₁ ζ t hi ht hζ hO =>
    exact False.elim (qTwo_family_imprimitive_excl f i₀ i₁ ζ t hi (Or.inr ⟨ht, hζ, hO⟩))
  | exc k hadm hdeg hord hcen hmax hclass hmodel =>
    have hk := qTwo_family_exc_excl k hadm hD.2.2.1 hdeg hd4 hcen
    subst hk
    exact False.elim (qTwo_family_H4_excl hdeg hord)
  | h4 hadm hdeg _ hneg hmax hclass => omega

end Dispatch

end CFSG.StandardType.QTwo

end
