module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Foundations.Basic
public import CFSG.Quasithin.Background.A1cModuleUnits

public section

namespace CFSG.Quasithin.InternalSec

open CFSG.Open

theorem exists_noncomm_of_isQuasisimple {Q : Type*} [Group Q] (hq : CFSG.IsQuasisimple Q) :
    ∃ a b : Q, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hq.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩

section Irr

variable {P : Type} [CommGroup P] {A : Subgroup (MulAut P)}

theorem eq_one_of_commOf_eq_bot (h : XMod.commOf ↥A (⊤ : Subgroup P) = ⊥) (a : ↥A) : a = 1 := by
  apply Subtype.ext
  ext s
  have hs : (a • s) * s⁻¹ ∈ XMod.commOf ↥A (⊤ : Subgroup P) :=
    Subgroup.subset_closure ⟨a, s, trivial, rfl⟩
  rw [h, Subgroup.mem_bot, mul_inv_eq_one] at hs
  exact hs

theorem commOf_top_of_irr (hirr : XMod.IsIrrSec ↥A (⊥ : Subgroup P) ⊤)
    (hnc : ∃ a b : ↥A, a * b ≠ b * a) : XMod.commOf ↥A (⊤ : Subgroup P) = ⊤ := by
  rcases hirr.2 _ (XMod.isInv_commOf (A := ↥A) (⊤ : Subgroup P)) bot_le le_top with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (by rw [eq_one_of_commOf_eq_bot h a, eq_one_of_commOf_eq_bot h b])
  · exact h

theorem isIrrSec_fixed_of_irr (hirr : XMod.IsIrrSec ↥A (⊥ : Subgroup P) ⊤)
    (hnc : ∃ a b : ↥A, a * b ≠ b * a) :
    XMod.IsIrrSec ↥A (XMod.fixed ↥A (⊤ : Subgroup P)) ⊤ := by
  refine ⟨?_, fun J hJ hfJ _ => ?_⟩
  · refine lt_of_le_of_ne le_top fun h => ?_
    obtain ⟨a, b, hab⟩ := hnc
    have htriv : ∀ c : ↥A, c = 1 := by
      intro c
      apply Subtype.ext
      ext s
      have hs : s ∈ XMod.fixed ↥A (⊤ : Subgroup P) := by rw [h]; trivial
      exact hs.2 c
    exact hab (by rw [htriv a, htriv b])
  · rcases hirr.2 J hJ bot_le le_top with h | h
    · left
      rw [h] at hfJ ⊢
      exact (le_bot_iff.1 hfJ).symm
    · right
      exact h

theorem isTwoReduced_of_irr [Finite P] (hP : ∀ p : P, p ^ 2 = 1)
    (hirr : XMod.IsIrrSec ↥A (⊥ : Subgroup P) ⊤) : XMod.IsTwoReduced ↥A (⊤ : Subgroup P) := by
  intro D hD hdk d hd l _
  let F : Subgroup P :=
    { carrier := {x | ∀ g ∈ D, g • x = x}
      one_mem' := fun g _ => smul_one g
      mul_mem' := fun {x y} hx hy g hg => by rw [smul_mul', hx g hg, hy g hg]
      inv_mem' := fun {x} hx g hg => by rw [smul_inv', hx g hg] }
  have hFinv : XMod.IsInv ↥A F := by
    intro a x hx g hg
    have hg' : a⁻¹ * g * a ∈ D := by
      have := hD.conj_mem g hg a⁻¹
      simpa using this
    have h1 := hx _ hg'
    calc g • (a • x) = a • ((a⁻¹ * g * a) • x) := by
          rw [← mul_smul, ← mul_smul]
          congr 1
          group
      _ = a • x := by rw [h1]
  have hD2 : IsPGroup 2 ↥D := by
    intro g
    obtain ⟨k, hk⟩ := hdk g g.2
    refine ⟨k, ?_⟩
    have hk' : ((g : ↥A) ^ 2 ^ k : ↥A) = 1 := by
      apply Subtype.ext
      ext x
      exact hk x trivial
    exact Subtype.ext (by simpa using hk')
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2P : 2 ∣ Nat.card P := by
    obtain ⟨x, -, hx⟩ := IsConcreteLE.exists_of_lt hirr.1
    have hx1 : x ≠ 1 := fun h => hx (by rw [h]; exact Subgroup.one_mem _)
    have hox : orderOf x = 2 := orderOf_eq_prime (hP x) hx1
    exact hox ▸ orderOf_dvd_natCard x
  have h1fix : (1 : P) ∈ MulAction.fixedPoints ↥D P := fun g => smul_one g
  obtain ⟨b, hb, hb1⟩ := hD2.exists_fixed_point_of_prime_dvd_card_of_fixed_point P h2P h1fix
  have hbF : b ∈ F := fun g hg => hb ⟨g, hg⟩
  rcases hirr.2 F hFinv bot_le le_top with h | h
  · exfalso
    have : b ∈ (⊥ : Subgroup P) := h ▸ hbF
    exact hb1 (Subgroup.mem_bot.1 this).symm
  · have hl : l ∈ F := by rw [h]; trivial
    exact hl d hd

theorem odd_card_eqvAut_of_irr [Finite P] (hP : ∀ p : P, p ^ 2 = 1)
    (hirr : XMod.IsIrrSec ↥A (⊥ : Subgroup P) ⊤) (hnc : ∃ a b : ↥A, a * b ≠ b * a) :
    Odd (Nat.card ↥(XMod.eqvAut ↥A P)) :=
  XMod.odd_card_eqvAut hP (commOf_top_of_irr hirr hnc) (isIrrSec_fixed_of_irr hirr hnc)
    (isTwoReduced_of_irr hP hirr)

end Irr

end CFSG.Quasithin.InternalSec
