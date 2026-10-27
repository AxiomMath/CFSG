module

public import CFSG.LocalAnalysis.StandardType.GGSixFieldFiveProof
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerE7
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUExc
public import CFSG.LieType.Steinberg.Isogeny.TwistedE6

public section

namespace CFSG.StandardType

namespace FieldFiveRank

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem

theorem le_of_psiDiagInner {G : Type} [Group G] {G₀ E : Subgroup G}
    (hC : Subgroup.centralizer (G₀ : Set G) = ⊥)
    (h : ∀ e ∈ E, ∃ g ∈ G₀, e * g ∈ Subgroup.centralizer (G₀ : Set G)) : E ≤ G₀ := by
  intro e he
  obtain ⟨g, hg, heg⟩ := h e he
  rw [hC, Subgroup.mem_bot] at heg
  rw [eq_inv_of_mul_eq_one_left heg]
  exact G₀.inv_mem hg

theorem card_lt_of_not_dvd {G : Type} [Group G] [Finite G] {G₀ E : Subgroup G}
    (hE : IsElemAbelian 5 E) (hEG : E ≤ G₀) {N : ℕ} (hN : Nat.card G₀ ∣ N)
    (h125 : ¬ 5 ^ 3 ∣ N) : Nat.card E < 5 ^ 4 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp : IsPGroup 5 E := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hdvd : 5 ^ k ∣ N := hk ▸ (Subgroup.card_dvd_of_le hEG).trans hN
  have hk2 : k ≤ 2 := by
    by_contra hk3
    exact h125 ((Nat.pow_dvd_pow 5 (by omega)).trans hdvd)
  rw [hk]
  calc 5 ^ k ≤ 5 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ < 5 ^ 4 := by norm_num

theorem not_dvd_ordF4 : ¬ 5 ^ 3 ∣ CFSG.Open.ordF4 2 := by
  unfold CFSG.Open.ordF4
  norm_num

theorem not_dvd_ordE6 : ¬ 5 ^ 3 ∣ CFSG.Open.ordE6 2 := by
  unfold CFSG.Open.ordE6
  norm_num

theorem units_eq_one_of_card_two {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2)
    (u : kˣ) : u = 1 := by
  classical
  have := Fintype.ofFinite k
  have h := FiniteField.pow_card_sub_one_eq_one (u : k) u.ne_zero
  rw [← Nat.card_eq_fintype_card, hk] at h
  exact Units.ext (by simpa using h)

theorem not_dvd_ordE7 : ¬ 5 ^ 3 ∣ CFSG.Open.ordE7 2 := by
  unfold CFSG.Open.ordE7
  norm_num

end FieldFiveRank

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  FieldFiveRank

theorem ggFieldFiveRankTag_F4 : GGFieldFiveRankTag .F4 := by
  intro G _ _ n ψ G₀ hpres hC E hE hEN hEdiag
  have hEG : E ≤ G₀ := le_of_psiDiagInner hC fun e he =>
    ggPsiDiagInner_F4 G n 1 ψ G₀ hpres e (hEN he) (hEdiag e he)
  have hrange : ψ.range = G₀ := hpres.2.1.1
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  have hU : Nat.card (ggU .F4 n 1).K = CFSG.Open.ordF4 2 := by
    show Nat.card ↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 (GaloisField 2 1)) = _
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hK]
  exact card_lt_of_not_dvd hE hEG (hrange ▸ hU ▸ Subgroup.card_range_dvd ψ) not_dvd_ordF4

theorem exists_mem_centralizer_E6_two {k : Type} [Field k] [Finite k] [CharP k 2]
    (hk : Nat.card k = 2) {G : Type*} [Group G]
    (ψ : ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup k) →* G)
    (hker : ψ.ker ≤ Subgroup.center ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup k))
    {c : G} (hc : GGPsiInnerDiag (CFSG.LieType.Steinberg.Minuscule.e6Datum k) ψ c) :
    ∃ g ∈ ψ.range, c * g ∈ Subgroup.centralizer (ψ.range : Set G) := by
  obtain ⟨g, hg, a, ha⟩ := PsiDiagChar.exists_char_E6 ψ hker hc
  refine ⟨g, hg, ?_⟩
  have hcl : Subgroup.closure {u | ∃ (i : Fin CFSG.Blueprint.Chevalley.Tag.E6.rank) (t : k),
      u = CFSG.LieType.Steinberg.Minuscule.e6Data_valid.xm k (Pi.single i 1) t ∨
      u = CFSG.LieType.Steinberg.Minuscule.e6Data_valid.xm k (-Pi.single i 1) t} ≤
      (Subgroup.centralizer {c * g}).comap ψ := by
    rw [Subgroup.closure_le]
    rintro u ⟨i, t, rfl | rfl⟩
    · have h1 := (ha i t).1
      rw [units_eq_one_of_card_two hk (a i), Units.val_one, one_mul] at h1
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      conv_rhs => rw [← h1]
      group
    · have h1 := (ha i t).2
      rw [units_eq_one_of_card_two hk (a i), inv_one, Units.val_one, one_mul] at h1
      rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      conv_rhs => rw [← h1]
      group
  rw [CFSG.LieType.Steinberg.Isogeny.closure_xm_simple_eq_top] at hcl
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨u, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp (hcl (Subgroup.mem_top u))

theorem ggFieldFiveRankTag_E6 : GGFieldFiveRankTag .E6 := by
  intro G _ _ n ψ G₀ hpres hC E hE hEN hEdiag
  have hrange : ψ.range = G₀ := hpres.2.1.1
  have hker := hpres.2.1.2
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEG : E ≤ G₀ := le_of_psiDiagInner hC fun e he => by
    obtain ⟨g, hg, hcg⟩ := exists_mem_centralizer_E6_two hK ψ hker (hEdiag e he)
    exact ⟨g, hrange ▸ hg, hrange ▸ hcg⟩
  have hZ : Subgroup.center ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup
      (GaloisField 2 1)) = ⊥ := by
    rw [← Subgroup.card_eq_one,
      (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 (GaloisField 2 1)).1, hK]
    rfl
  have hinj : Function.Injective (CFSG.LieType.Steinberg.Isogeny.e6Isogeny (GaloisField 2 1)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    exact CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center (GaloisField 2 1)
  have hA : Nat.card ↥(CFSG.Blueprint.Chevalley.adjointGroup .E6 (GaloisField 2 1)) =
      CFSG.Open.ordE6 2 := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6, hK]
  have hU : Nat.card (ggU .E6 n 1).K ∣ CFSG.Open.ordE6 2 := by
    show Nat.card ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField 2 1)) ∣ _
    rw [← hA, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  exact card_lt_of_not_dvd hE hEG ((hrange ▸ Subgroup.card_range_dvd ψ).trans hU) not_dvd_ordE6

theorem ggFieldFiveRankTag_E7 : GGFieldFiveRankTag .E7 := by
  intro G _ _ n ψ G₀ hpres hC E hE hEN hEdiag
  have hEG : E ≤ G₀ := le_of_psiDiagInner hC fun e he =>
    ggPsiDiagInner_E7 G n 1 ψ G₀ hpres e (hEN he) (hEdiag e he)
  have hrange : ψ.range = G₀ := hpres.2.1.1
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Subgroup.center ↥(CFSG.LieType.Steinberg.Minuscule.e7Data_valid.minGroup
      (GaloisField 2 1)) = ⊥ := by
    rw [← Subgroup.card_eq_one,
      (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e7 (GaloisField 2 1)).1, hK]
    rfl
  have hinj : Function.Injective (CFSG.LieType.Steinberg.Isogeny.e7Isogeny (GaloisField 2 1)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    exact CFSG.ClassicalInvolution.ModelFacts.ChevAut.e7Isogeny_ker_le_center (GaloisField 2 1)
  have hA : Nat.card ↥(CFSG.Blueprint.Chevalley.adjointGroup .E7 (GaloisField 2 1)) =
      CFSG.Open.ordE7 2 := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7, hK]
  have hU : Nat.card (ggU .E7 n 1).K ∣ CFSG.Open.ordE7 2 := by
    show Nat.card ↥(CFSG.LieType.Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField 2 1)) ∣ _
    rw [← hA, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  exact card_lt_of_not_dvd hE hEG ((hrange ▸ Subgroup.card_range_dvd ψ).trans hU) not_dvd_ordE7

end CFSG.StandardType
