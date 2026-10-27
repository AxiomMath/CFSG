module

public import CFSG.Quasithin.Background.SzG11G94D4
public import CFSG.Quasithin.Background.SzG11G94D6
public import CFSG.Quasithin.EmptyFaithful.SzN31SmallFinal
public import CFSG.Quasithin.EmptyFaithful.SzN32Final

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzG11G94

open CFSG.Quasithin.G11 CFSG.Open CFSG.Quasithin.SzN31

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem smallOdd_core {Γ A : Subgroup (GLV V)} {m : ℕ} (hyp : G94Hyp Γ A m)
    (hodd : Odd (Module.finrank (ZMod 2) V)) : False := by
  have h3 := SmOdd.pCoreOf_three_eq_bot_of_odd hyp hodd
  have hcent : ∀ p : ℕ, p.Prime → p ≠ 2 →
      A ≤ Subgroup.centralizer (pCoreOf p Γ : Set (GLV V)) := by
    intro p hp hp2
    by_cases hp3 : p = 3
    · subst hp3
      rw [h3]
      intro a _
      exact Subgroup.mem_centralizer_iff.mpr fun g hg => by rw [Subgroup.mem_bot.mp hg]; simp
    · have h5 : 5 ≤ p := by
        have := hp.two_le
        by_contra h
        interval_cases p
        · exact hp2 rfl
        · exact hp3 rfl
        · exact absurd hp (by decide)
      by_contra hnot
      have hd4 := (counting_prime_ge_five hyp hp h5 hnot).2.2
      rw [hd4] at hodd
      exact absurd hodd (by decide)
  have hA : A = ⊥ := g94_eq_bot_of_le_centralizer_pCoreOf hyp le_rfl hcent
  have h1 := hyp.A_card
  rw [hA, Subgroup.card_bot] at h1
  have h2 := Nat.one_lt_two_pow (n := m) (by have := hyp.A_ne; omega)
  omega

theorem solvable_of_finrank_two {Γ : Subgroup (GLV V)} (hd : Module.finrank (ZMod 2) V = 2) :
    Group.IsSolvable ↥Γ := by
  have hV : Nat.card V = 4 := by
    have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
    norm_num
  have hN : Nat.card {v : V // v ≠ 0} = 3 := SmD2.card_nonzero_of_card_four hV
  set φ : ↥Γ →* Equiv.Perm {v : V // v ≠ 0} := (SmD2.permNonzeroHom V).comp Γ.subtype with hφdef
  have hφ : Function.Injective φ := SmD2.permNonzeroHom_injective.comp Γ.subtype_injective
  have hperm : Nat.card (Equiv.Perm {v : V // v ≠ 0}) = 6 := by
    rw [Nat.card_perm, hN]
    rfl
  have hdvd : Nat.card ↥Γ ∣ 6 := hperm ▸ Subgroup.card_dvd_of_injective φ hφ
  exact isSolvable_of_card_dvd_two_pow_mul_three_pow (a := 1) (b := 1) (by simpa using hdvd)

theorem g94_nonsolv (hT : SylowGL6NoCover) {Γ A : Subgroup (GLV V)} {m : ℕ}
    (hyp : G94Hyp Γ A m) (hns : ¬ Group.IsSolvable ↥Γ) : G94Concl Γ A m := by
  have hk : KCFor Γ := g94KC_of_factR factR V Γ hyp.quotient
  have hm : m ≤ 2 := by
    have hk3 := hk 3 Nat.prime_three (by norm_num) (pCoreOf 3 Γ) A (Subgroup.map_subtype_le _)
      hyp.A_le (isPGroup_pCoreOf 3 Γ)
      (fun b hb => ⟨by rw [← pow_two]; exact hyp.A_elem.2 b hb, fun c hc =>
        G8.commute_of_isElemAbelian hyp.A_elem hb hc⟩)
      (fun b hb x hx => pCoreOf_normal_conj 3 Γ b (hyp.A_le hb) x hx)
    exact counting_bound hyp hk3
  have hd : Module.finrank (ZMod 2) V ≤ 6 := by
    have := hyp.bound
    omega
  have hpos : 0 < Module.finrank (ZMod 2) V := by
    have hne : (⊤ : Submodule (ZMod 2) V) ≠ ⊥ := hyp.irreducible.ne_bot
    have : Nontrivial V := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      exact hne (Subsingleton.elim _ _)
    exact Module.finrank_pos
  obtain ⟨d, hd'⟩ : ∃ d, Module.finrank (ZMod 2) V = d := ⟨_, rfl⟩
  rw [hd'] at hd hpos
  interval_cases d
  · exact (smallOdd_core hyp (by rw [hd']; exact ⟨0, rfl⟩)).elim
  · exact absurd (solvable_of_finrank_two hd') hns
  · exact (smallOdd_core hyp (by rw [hd']; exact ⟨1, rfl⟩)).elim
  · exact smallCase4_ns hyp hns hm hd'
  · exact (smallOdd_core hyp (by rw [hd']; exact ⟨2, rfl⟩)).elim
  · have hm2 : m = 2 := by
      have := hyp.bound
      omega
    subst hm2
    have hC : Ctx0 Γ A :=
      ⟨hyp, hd', fun S hSΓ hSp => SmD6.card_le_27_of_isPGroup hT hd' hyp.quotient hSΓ hSp⟩
    exact absurd hC.isSolvable hns

end CFSG.Quasithin.SzG11G94

namespace CFSG.Quasithin.SzG11

theorem g94Stmt_proved : G11.G94Stmt := by
  intro V _ _ _ Γ A m hyp
  by_cases hs : Group.IsSolvable ↥Γ
  · exact SzN31.g94StmtSolv_of_T SzN32.sylowGL6NoCover_proved V Γ A m hyp hs
  · exact SzG11G94.g94_nonsolv SzN32.sylowGL6NoCover_proved hyp hs

end CFSG.Quasithin.SzG11
