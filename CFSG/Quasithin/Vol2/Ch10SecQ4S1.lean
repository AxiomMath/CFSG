module

public import CFSG.Quasithin.Vol2.Ch10SecE22Two

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem e23Concl_H (he23 : E2.E23Statement) (h1021 : Ch10.Stmt10_2_1) (h331 : Stmt3_3_1)
    (hyp : Hyp10 G T L I) {H : Subgroup G} (hH : IsHStar T (fsuM T L) H)
    (hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥) (hn3 : ¬ Ch10.Case10_1_1Three T L I) :
    ∃ hel : IsElemAbelian 2 (VZ T H), E2.E23Concl H T (VZ T H) hel := by
  have hmp := SecB.minParabolic_of_isHStar h331 hyp hH
  obtain ⟨S, hS⟩ := CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo hyp.fsu.sylow
  have hchar : CharTwo H := charTwo_of_inH hyp.fsu.qtke.2.1 S (hS ▸ hH.1)
  obtain ⟨-, hel, hW⟩ := conjClosure_isTwoReducedIn_of_charTwo hmp.isSylow hchar
    (le_refl (quasithinOmegaOneCenter T))
  have := hyp.fsu.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  have hSQ : SQTKGroup ↥H := InternalSec.sqtkGroup_of_localSQTK hK hH.1.2
  have hJW := (SecE.stmt10_2_2_two h1021 h331 hyp hH hZH hn3).2.1
  exact ⟨hel, he23 G H T _ (VZ T H) hel hmp hSQ hchar hW hJW⟩

theorem isA5Module_of_not_isSylowTwoOf {H : Subgroup G} {hel : IsElemAbelian 2 (VZ T H)}
    (hc : E2.E23Concl H T (VZ T H) hel)
    (hsyl : ¬ IsSylowTwoOf (baum T) (oTwoUpper H ⊔ baum T)) :
    ∃ I : Finset (Subgroup (MulAut (IntMod (VZ T H) hel))), (I.card = 1 ∨ I.card = 2) ∧
      autI hel (thompsonJ H) = (⨆ K ∈ I, K) ∧
      (∀ K ∈ I, ∀ K' ∈ I, K ≠ K' → ∀ a ∈ K, ∀ b ∈ K', a * b = b * a) ∧
      (∀ K ∈ I, ∀ K' ∈ I, ∃ t ∈ autI hel T, B1.conjAut t K = K') ∧
      ∀ K ∈ I, E2.IsA5Module K := by
  obtain ⟨-, I, hcard, hsup, hcomm, -, hconj, htype, -, -, h2, -⟩ := hc
  refine ⟨I, hcard, hsup, hcomm, hconj, ?_⟩
  have key : ∀ n : ℕ, 2 ^ n * (4 ^ n - 1) ≠ 120 := by
    intro n hn
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n <;> simp_all
    · have h8 : 8 ≤ 2 ^ n :=
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
      have h64 : 64 ≤ 4 ^ n :=
        calc 64 = 4 ^ 3 := by norm_num
          _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) h
      have : 8 * 63 ≤ 2 ^ n * (4 ^ n - 1) := Nat.mul_le_mul h8 (by omega)
      omega
  by_contra hall
  push Not at hall
  obtain ⟨K₀, hK₀, hK₀a⟩ := hall
  have hL2 : ∀ K ∈ I, ∃ n : ℕ,
      E2.IsL2Natural K (fixV (autI hel (twoResidual H))) n := by
    intro K hK
    rcases htype K hK with h | h
    · exact h
    · exfalso
      obtain ⟨t, -, ht⟩ := hconj K hK K₀ hK₀
      rcases htype K₀ hK₀ with ⟨n, hn⟩ | h0
      · have h1 := SecA.card_of_isL2Natural hn
        rw [← ht, SecA.card_conjAut, SecA.card_of_isA5Module h] at h1
        exact key n h1.symm
      · exact hK₀a h0
  obtain ⟨-, -, h3, -⟩ := h2 hL2
  apply hsyl
  rwa [SecE.twoResidual_eq_oTwoUpper] at h3

end CFSG.Quasithin.Vol2.Ch10.SecF.C10E4
