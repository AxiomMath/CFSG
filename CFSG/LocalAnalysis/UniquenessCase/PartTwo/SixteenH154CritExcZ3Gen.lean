module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.LocalAnalysis.SolvableSignalizer.CoprimeAction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s16h_card_dvd_sub_of_fixedBy {E X : Type*} [Group E] [Finite E] [MulAction E X]
    [Finite X] {N f : ℕ} (hN : Nat.card X = N) (hfN : f ≤ N)
    (hf : ∀ g : E, g ≠ 1 → Nat.card ↥(MulAction.fixedBy X g) = f) :
    Nat.card E ∣ N - f := by
  classical
  haveI : Fintype E := Fintype.ofFinite E
  haveI : Fintype X := Fintype.ofFinite X
  haveI : ∀ g : E, Fintype ↥(MulAction.fixedBy X g) := fun g => Fintype.ofFinite _
  haveI : Fintype (MulAction.orbitRel.Quotient E X) := Fintype.ofFinite _
  have key := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group E X
  simp only [Fintype.card_eq_nat_card] at key
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : E))] at key
  have h1 : Nat.card ↥(MulAction.fixedBy X (1 : E)) = N := by
    rw [MulAction.fixedBy_one_eq_univ, Nat.card_univ, hN]
  have h2 : ∑ g ∈ Finset.univ.erase (1 : E), Nat.card ↥(MulAction.fixedBy X g) =
      (Nat.card E - 1) * f := by
    rw [Finset.sum_congr rfl (fun g hg => hf g (Finset.ne_of_mem_erase hg)), Finset.sum_const,
      smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card]
  rw [h1, h2] at key
  have hn : 0 < Nat.card E := Nat.card_pos
  obtain ⟨o, ho⟩ : ∃ o, o = Nat.card (MulAction.orbitRel.Quotient E X) := ⟨_, rfl⟩
  rw [← ho] at key
  generalize Nat.card E = n at key hn ⊢
  rcases n with _ | m
  · omega
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hfN
    have e1 : f + a - f = a := by omega
    have e2 : m + 1 - 1 = m := by omega
    rw [e1]
    rw [e2] at key
    have h3 : (m + 1) * f + a = o * (m + 1) := by linarith
    exact (Nat.dvd_add_right (dvd_mul_right (m + 1) f)).1 (h3 ▸ dvd_mul_left (m + 1) o)

theorem s16h_card_dvd_sub_of_fix_card {W : Type} [CommGroup W] [Finite W]
    {R : Subgroup (MulAut W)} {U : Subgroup W} (hU : ∀ x ∈ R, ∀ u ∈ U, x u ∈ U) {c : ℕ}
    (hR : ∀ x ∈ R, x ≠ 1 → Nat.card ↥(U ⊓ fixV (zpowers x)) = c) :
    Nat.card ↥R ∣ Nat.card ↥U - c := by
  classical
  rcases Subgroup.bot_or_exists_ne_one R with hbot | ⟨x₀, hx₀R, hx₀ne⟩
  · rw [hbot, Subgroup.card_bot]
    exact one_dvd _
  · have hcU : c ≤ Nat.card ↥U := by
      rw [← hR x₀ hx₀R hx₀ne]
      exact Subgroup.card_le_of_le inf_le_left
    letI : MulAction ↥R ↥U :=
      { smul := fun x u => ⟨x.1 u.1, hU x.1 x.2 u.1 u.2⟩
        one_smul := fun u => Subtype.ext rfl
        mul_smul := fun x y u => Subtype.ext rfl }
    have hsmul : ∀ (y : ↥R) (w : ↥U), ((y • w : ↥U) : W) = y.1 w.1 := fun _ _ => rfl
    have hfix : ∀ x : ↥R, x ≠ 1 → Nat.card ↥(MulAction.fixedBy ↥U x) = c := by
      intro x hx
      have hx' : (x : MulAut W) ≠ 1 := fun h => hx (Subtype.ext h)
      have hcard : Nat.card ↥(MulAction.fixedBy ↥U x) =
          Nat.card ↥(U ⊓ fixV (zpowers (x : MulAut W))) := by
        refine Nat.card_congr
          { toFun := fun u =>
              ⟨u.1.1, Subgroup.mem_inf.mpr
                ⟨u.1.2, mem_fixV_zpowers_iff_apply.mpr (by
                  rw [← hsmul x u.1]
                  exact congrArg (fun w : ↥U => (w : W)) u.2)⟩⟩
            invFun := fun v =>
              ⟨⟨v.1, (Subgroup.mem_inf.mp v.2).1⟩,
                Subtype.ext (mem_fixV_zpowers_iff_apply.mp (Subgroup.mem_inf.mp v.2).2)⟩
            left_inv := fun u => Subtype.ext (Subtype.ext rfl)
            right_inv := fun v => Subtype.ext rfl }
      rw [hcard, hR (x : MulAut W) x.2 hx']
    exact s16h_card_dvd_sub_of_fixedBy rfl hcU hfix

theorem s16h_eq_top_of_fixV_le {W : Type} [CommGroup W] [Finite W] {p : ℕ} (hp : p.Prime)
    (hW : ¬ p ∣ Nat.card W) {E : Subgroup (MulAut W)} (hE : IsElemAbelian p E)
    (hcard : p ^ 2 ≤ Nat.card ↥E) {F : Subgroup W}
    (hF : ∀ x ∈ E, x ≠ 1 → fixV (zpowers x) ≤ F) : F = ⊤ := by
  letI : IsMulCommutative ↥E := hE.1
  letI : CommGroup ↥E := IsMulCommutative.instCommGroup
  haveI : CFSG.IsElementaryAbelian p ↥E :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one
        (fun x : ↥E => Subtype.ext (hE.2 x.1 x.2)) }
  let α : ↥E →* MulAut W :=
    { toFun := fun a => (a : MulAut W)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hgen := CFSG.SolvableSignalizer.iSup_fixedSubgroup_eq_top (A := ↥E) (G := W) p hp
    α hcard hW
  refine le_antisymm le_top ?_
  calc ⊤ = ⨆ (a : ↥E) (_ : a ≠ 1), CFSG.SolvableSignalizer.fixedSubgroup α a := hgen.symm
    _ ≤ F := by
      refine iSup_le fun a => iSup_le fun ha => ?_
      intro v hv
      have hmem : (a : MulAut W) v = v :=
        (CFSG.SolvableSignalizer.mem_fixedSubgroup α a v).mp hv
      exact hF (a : MulAut W) a.2 (fun h => ha (Subtype.ext h))
        (mem_fixV_zpowers_iff_apply.mpr hmem)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
