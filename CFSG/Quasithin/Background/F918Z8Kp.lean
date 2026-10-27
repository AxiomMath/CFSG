module

public import CFSG.Quasithin.Background.F918Z8Ka

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge
open scoped Pointwise

theorem lp2_four_le_two_pow {n : ℕ} (hn : 2 ≤ n) : 4 ≤ 2 ^ n :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem lp2_isPSL_of_equiv {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) {X : Type} [Group X]
    (e : X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K)) : IsPSL 2 2 n X := by
  have hchar : CharP K 2 := F918X.NatSL2.charP_two_of_card hK
  have h4 := lp2_four_le_two_pow hn
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, K, inferInstance, inferInstance, hK,
    ⟨e.trans ((specialLinearGroupEquivStatedSL 2 K).symm.trans
      CFSG.QuasithinUnique.Vol2Native.A312L.sl2EquivStatedProj)⟩⟩
  all_goals
    intro h
    have := congrArg Prod.snd h
    simp only at this
    omega

theorem lp2_isSimpleGroup_statedSL {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) : IsSimpleGroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) := by
  have hchar : CharP K 2 := F918X.NatSL2.charP_two_of_card hK
  have h4 : 4 ≤ Nat.card K := hK ▸ lp2_four_le_two_pow hn
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.QuasithinUnique.Vol2Native.A312L.sl2_isSimple
      (CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four h4)
  exact MulEquiv.isSimpleGroup (specialLinearGroupEquivStatedSL 2 K).symm

variable {Y : Type} [CommGroup Y] [Finite Y] {Γ Λ S : Subgroup (MulAut Y)} {V : Subgroup Y}

theorem loc_isPSL_two (h : LocCfg Γ Λ S V) {n : ℕ} (hn : 2 ≤ n)
    (hnat : BinaryNaturalSL (autSub Λ V) ⊤ ⊥ 2 n) : IsPSL 2 2 n ↥Λ := by
  obtain ⟨K, hKf, hKfin, hK, π₀, hπ⟩ := hnat
  let π : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) →* ↥(autSub Λ V) := π₀
  have hπs : Function.Surjective π := hπ.1
  have hsimp : IsSimpleGroup ↥Λ := insp5a_sec_isSimpleGroup h.a38
  obtain ⟨hID, -, -⟩ := loc_irr_data h
  obtain ⟨eΛ⟩ := CaseIISec.equiv hsimp hID (loc_nontriv h)
  have hS : IsSimpleGroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) :=
    lp2_isSimpleGroup_statedSL hn hK
  have hker : π.ker = ⊥ := by
    rcases hS.eq_bot_or_eq_top_of_normal π.ker with h0 | h0
    · exact h0
    · exfalso
      have hsub : Subsingleton ↥(autSub Λ V) := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨x, rfl⟩ := hπs a
        obtain ⟨y, rfl⟩ := hπs b
        have hx : π x = 1 := by rw [← MonoidHom.mem_ker, h0]; trivial
        have hy : π y = 1 := by rw [← MonoidHom.mem_ker, h0]; trivial
        rw [hx, hy]
      have hsubΛ : Subsingleton ↥Λ := eΛ.toEquiv.subsingleton
      obtain ⟨a, b, hab⟩ := exists_pair_ne ↥Λ
      exact hab (Subsingleton.elim a b)
  have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hker
  let eπ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 K) ≃* ↥(autSub Λ V) :=
    MulEquiv.ofBijective π ⟨hinj, hπs⟩
  exact lp2_isPSL_of_equiv hn hK (eΛ.trans eπ.symm)

end CFSG.Quasithin
