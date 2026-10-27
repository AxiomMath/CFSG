module

public import CFSG.Quasithin.EmptyFaithful.Gold14610LiftMaps
public import CFSG.Quasithin.EmptyFaithful.Gold14610LiftSL2
public import CFSG.Quasithin.Background.A3Structure313Core
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native

namespace Gold14610

variable {G : Type} [Group G] [Finite G] {I K : Subgroup G}

theorem exists_sl2_of_case34 {X : Type} [Group X] (hcommon : A36Common X)
    (h34 : A36Case3 X ∨ A36Case4 X) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ IsSL2 q (X ⧸ CFSG.oddCore X) := by
  have hF := hcommon.1
  rcases h34 with ⟨p, hp, hp3, -, -, hnat⟩ | h4
  · exact ⟨p, hp, by omega, A313.isSL2_quotient_of_natural hF hnat⟩
  · exact ⟨5, Nat.prime_five, by norm_num,
      IsSL2.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hF) h4.2.2.1⟩

theorem two_ne_zero_zmod {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : (2 : ZMod q) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 this)

theorem isQuasisimple_pCore_quotient (hloc : LocalSQTK G) (h36 : A36CoreForSQTKCat)
    (hI : pCoreOf 2 I ≠ ⊥) (hKc : K ∈ cComp I)
    (hsyl : IsSylowTwoOf (Open.pCore 2 ↥I) (CFSG.pPrimeCore 3 ↥I))
    (hB : CFSG.IsQuasisimple ↥(imgMod3 I K))
    (hcen : ∀ z ∈ Subgroup.center ↥(imgMod3 I K), ¬ Even (orderOf z)) :
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
  have hKI : K ≤ I := le_of_mem_cComp hKc
  obtain ⟨hcases, hcommon, -⟩ := lemma_1_2_1_four_core hloc h36 hI hKc
  obtain ⟨e⟩ := modO2_mulEquiv hKc
  rcases hcases with hc | h34
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hc.1
  · exfalso
    obtain ⟨q, hq, hq2, ⟨e₂⟩⟩ := exists_sl2_of_case34 hcommon h34
    have h2 := two_ne_zero_zmod hq hq2
    let X := ↥(modO2Image I K)
    let ψ : ↥K →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q) :=
      e₂.toMonoidHom.comp ((QuotientGroup.mk' (CFSG.oddCore X)).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K))))
    have hψ : Function.Surjective ψ :=
      e₂.surjective.comp ((QuotientGroup.mk'_surjective _).comp
        (e.surjective.comp (QuotientGroup.mk'_surjective _)))
    have hsub : IsSubnormal K I := subnormal_of_mem_cComp hKc
    have hker : CFSG.pCore 2 ↥K ≤ (toImg hKI).ker := pCore_le_ker_toImg hKI hsub
    refine false_of_sl2_cover h2 hB (toImg hKI) (toImg_surjective hKI) ψ hψ hcen ?_ ?_
    · intro x hx
      have hx1 : e₂ ((QuotientGroup.mk' (CFSG.oddCore X))
          (e (QuotientGroup.mk' (CFSG.pCore 2 ↥K) x))) = 1 := hx
      have hx2 : (QuotientGroup.mk' (CFSG.oddCore X))
          (e (QuotientGroup.mk' (CFSG.pCore 2 ↥K) x)) = 1 :=
        e₂.injective (by rw [hx1, map_one])
      have hx3 : e (QuotientGroup.mk' (CFSG.pCore 2 ↥K) x) ∈ CFSG.oddCore X :=
        (QuotientGroup.eq_one_iff _).mp hx2
      refine ⟨Nat.card (CFSG.oddCore X), A312.odd_card_oddCore X, ?_⟩
      have h4 : (e (QuotientGroup.mk' (CFSG.pCore 2 ↥K) x)) ^ Nat.card (CFSG.oddCore X) = 1 := by
        have := pow_card_eq_one' (G := ↥(CFSG.oddCore X)) (x := ⟨_, hx3⟩)
        exact congrArg Subtype.val this
      have h5 : x ^ Nat.card (CFSG.oddCore X) ∈ CFSG.pCore 2 ↥K := by
        have h6 : e (QuotientGroup.mk' (CFSG.pCore 2 ↥K) (x ^ Nat.card (CFSG.oddCore X))) = 1 := by
          rw [map_pow, map_pow]
          exact h4
        have h7 := e.injective (h6.trans (map_one e).symm)
        exact (QuotientGroup.eq_one_iff _).mp h7
      rw [← map_pow]
      exact MonoidHom.mem_ker.mp (hker h5)
    · intro x hx
      have hx0 : toD hKI x = 1 := (toD_eq_one_iff hKI x).mpr ((mem_ker_toImg hKI x).mp hx)
      obtain ⟨m, hm, hxm⟩ := exists_odd_pow_mem_pCore_K hKI hsyl hx0
      refine ⟨m, hm, ?_⟩
      rw [← map_pow]
      have h8 : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (x ^ m) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hxm
      show e₂ ((QuotientGroup.mk' (CFSG.oddCore X))
        (e (QuotientGroup.mk' (CFSG.pCore 2 ↥K) (x ^ m)))) = 1
      rw [h8, map_one, map_one, map_one]

end Gold14610

end CFSG.Quasithin
