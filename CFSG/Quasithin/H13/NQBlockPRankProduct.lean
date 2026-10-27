module

public import CFSG.Quasithin.H13.NQBlockThompsonTransport
public import CFSG.Quasithin.Background.A3FactsRank

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup

theorem pRank_eq_zero_of_subsingleton {A : Type*} [Group A] [Finite A] [Subsingleton A]
    {p : ℕ} (hp : 1 < p) : CFSG.pRank p A = 0 := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine Nat.le_zero.mp (CFSG.SectionRank.pRank_le hp fun E _ _ => ?_)
  rw [pow_zero]
  exact Finite.card_le_one_iff_subsingleton.mpr inferInstance

theorem pRank_prod_le {S T : Type*} [Group S] [Group T] [Finite S] [Finite T] {p : ℕ}
    (hp : p.Prime) :
    CFSG.Open.pRank p (⊤ : Subgroup (S × T)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup S) + CFSG.Open.pRank p (⊤ : Subgroup T) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup (S × T))
  have hEcomm : ∀ a b : E, a * b = b * a := fun a b => hE.1.is_comm.comm a b
  set φ : ↥E →* T := (MonoidHom.snd S T).comp E.subtype with hφdef
  have hφr : φ.range = E.map (MonoidHom.snd S T) := by
    rw [hφdef, MonoidHom.range_comp, range_subtype]
  have hrel : CFSG.Open.IsElemAbelian p (E.map (MonoidHom.snd S T)) :=
    CFSG.SectionRank.isElemAbelian_map hE _
  have hr2 : IsPGroup p ↥(E.map (MonoidHom.snd S T)) := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hrel.2 g g.2)⟩
  obtain ⟨a, ha⟩ := hr2.exists_card_eq
  have ha' : a ≤ CFSG.Open.pRank p (⊤ : Subgroup T) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_top hrel ha
  have hk2 : IsPGroup p ↥φ.ker := fun g => ⟨1, Subtype.ext (Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_one]
    exact hE.2 _ (g : ↥E).2))⟩
  obtain ⟨b, hb⟩ := hk2.exists_card_eq
  have hb' : b ≤ CFSG.Open.pRank p (⊤ : Subgroup S) := by
    refine CFSG.SectionRank.le_pRank_of_injective (A := ↥φ.ker) hp.one_lt
      (fun x y => Subtype.ext (hEcomm x y)) (fun x => Subtype.ext (Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_one]
        exact hE.2 _ (x : ↥E).2))) hb
      ((MonoidHom.fst S T).comp (E.subtype.comp φ.ker.subtype)) ?_ le_top
    intro x y hxy
    have hx : ((x : ↥E) : S × T).2 = 1 := MonoidHom.mem_ker.mp x.2
    have hy : ((y : ↥E) : S × T).2 = 1 := MonoidHom.mem_ker.mp y.2
    exact Subtype.ext (Subtype.ext (Prod.ext hxy (hx.trans hy.symm)))
  have hcard : Nat.card ↥E = Nat.card ↥(E.map (MonoidHom.snd S T)) * Nat.card ↥φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hφr]
  rw [hEc, ha, hb, ← pow_add] at hcard
  have := Nat.pow_right_injective hp.two_le hcard
  omega

theorem pRank_prod_eq {S T : Type} [Group S] [Group T] [Finite S] [Finite T] {p : ℕ}
    (hp : p.Prime) : CFSG.pRank p (S × T) = CFSG.pRank p S + CFSG.pRank p T := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top,
    CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact le_antisymm (pRank_prod_le hp) (A3Facts.pRank_prod_ge hp.one_lt)

def piOptionMulEquivProd {ι : Type*} (G : Option ι → Type*) [∀ i, Group (G i)] :
    (∀ i, G i) ≃* G none × ∀ i : ι, G (some i) :=
  { Equiv.piOptionEquivProd with map_mul' := fun _ _ => rfl }

def piCongrLeftMulEquiv' {ι ι' : Type*} (G : ι → Type*) [∀ i, Group (G i)] (e : ι ≃ ι') :
    (∀ i, G i) ≃* ∀ j : ι', G (e.symm j) :=
  { Equiv.piCongrLeft' G e with map_mul' := fun _ _ => rfl }

theorem pRank_pi_eq {ι : Type} [Fintype ι] (G : ι → Type) [∀ i, Group (G i)]
    [∀ i, Finite (G i)] {p : ℕ} (hp : p.Prime) :
    CFSG.pRank p (∀ i, G i) = ∑ i, CFSG.pRank p (G i) := by
  have : Fact p.Prime := ⟨hp⟩
  revert G
  refine Finite.induction_empty_option (P := fun ι => ∀ [Fintype ι] (G : ι → Type)
    [∀ i, Group (G i)] [∀ i, Finite (G i)], CFSG.pRank p (∀ i, G i) = ∑ i, CFSG.pRank p (G i))
    ?_ ?_ ?_ ι
  · intro α β e hα _ G _ _
    have : Fintype α := Fintype.ofEquiv β e.symm
    have h1 := hα (fun a => G (e a))
    have h2 : CFSG.pRank p (∀ b, G b) = CFSG.pRank p (∀ a, G (e a)) :=
      pRank_mulEquiv (piCongrLeftMulEquiv' G e.symm) p
    rw [h2, h1]
    exact Fintype.sum_equiv e _ _ fun _ => rfl
  · intro _ G _ _
    rw [pRank_eq_zero_of_subsingleton hp.one_lt]
    simp
  · intro α _ hα _ G _ _
    rw [pRank_mulEquiv (piOptionMulEquivProd G) p, pRank_prod_eq hp, hα]
    obtain rfl : ‹Fintype (Option α)› = instFintypeOption := Subsingleton.elim _ _
    exact (Fintype.sum_option (fun i => CFSG.pRank p (G i))).symm

end CFSG.Quasithin.H13.NQBlock
