module

public import CFSG.Quasithin.Vol2.Ch11SecA04Hyp319
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Vol2.Ch11SecA02Card
public import CFSG.Quasithin.Vol2.Ch11SecA11Setup
public import CFSG.Quasithin.Vol2.Ch1ModO2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

section Abstract

variable {X : Type} [Group X] [Finite X] {K : Type} [Field K] [Finite K] {n : ℕ}

theorem card_of_quot_SL2 (hK : Nat.card K = 2 ^ n)
    (e : X ⧸ CFSG.pCore 2 X ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    ∃ a, Nat.card X = 2 ^ (a + n) * oSL2 n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := X))
  refine ⟨a, ?_⟩
  rw [(CFSG.pCore 2 X).card_eq_card_quotient_mul_card_subgroup, Nat.card_congr e.toEquiv,
    card_SL_two hK, ha, pow_add]
  ring

theorem oddCore_eq_bot_of_quot_SL2 (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (e : X ⧸ CFSG.pCore 2 X ≃* Matrix.SpecialLinearGroup (Fin 2) K) : CFSG.oddCore X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) := isSimpleGroup_SL2 hn hK
  have hs : IsSimpleGroup (X ⧸ CFSG.pCore 2 X) := e.isSimpleGroup
  have hNn : ((CFSG.oddCore X).map (QuotientGroup.mk' (CFSG.pCore 2 X))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hodd : Odd (Nat.card (CFSG.oddCore X)) := A37.odd_card_oddCore X
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((CFSG.oddCore X).map (QuotientGroup.mk' (CFSG.pCore 2 X))) with hbot | htop
  · have hle : CFSG.oddCore X ≤ CFSG.pCore 2 X := by
      intro x hx
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 X) x ∈
          (CFSG.oddCore X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) := ⟨x, hx, rfl⟩
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp ((CFSG.pCore_isPGroup (p := 2) (G := X)).to_le hle)
    rw [hk] at hodd
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hk0).mpr even_two)
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  · exfalso
    have h1 := Subgroup.card_map_dvd (H := CFSG.oddCore X) (QuotientGroup.mk' (CFSG.pCore 2 X))
    rw [htop, Subgroup.card_top, Nat.card_congr e.toEquiv, card_SL_two hK] at h1
    have h2 : 2 ∣ Nat.card (CFSG.oddCore X) :=
      dvd_trans (dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _) h1
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

end Abstract

structure BarData {Q : Type} [Group Q] (B : Subgroup Q) (n : ℕ) : Prop where
  two_le : 2 ≤ n
  card : ∃ a, Nat.card ↥B = 2 ^ (a + n) * oSL2 n
  cardQ : Nat.card (ModO2 B) = 2 ^ n * oSL2 n
  odd : ∀ N : Subgroup ↥B, N.Normal → Odd (Nat.card N) → N = ⊥

theorem barData_of_quot_SL2 {Q : Type} [Group Q] [Finite Q] {B : Subgroup Q} {K : Type}
    [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (e : ModO2 B ≃* Matrix.SpecialLinearGroup (Fin 2) K) : BarData B n where
  two_le := hn
  card := card_of_quot_SL2 hK e
  cardQ := by rw [Nat.card_congr e.toEquiv, card_SL_two hK]
  odd := fun N hN hodd => by
    have h1 : N ≤ CFSG.oddCore ↥B := le_sSup ⟨hN, hodd⟩
    rw [oddCore_eq_bot_of_quot_SL2 hn hK e] at h1
    exact eq_bot_iff.mpr h1

variable {G : Type} [Group G] [Finite G]

theorem modO2Image_quotEquiv {H B : Subgroup G} (hBH : B ≤ H) :
    Nonempty (ModO2 B ≃* ModO2 (modO2Image H B)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).subgroupMap (B.subgroupOf H) with hρ
  have hsurj : Function.Surjective ρ := MonoidHom.subgroupMap_surjective _ _
  have hker : IsPGroup 2 ↥ρ.ker := by
    intro x
    have hx : ((x : ↥(B.subgroupOf H)) : ↥H) ∈ CFSG.pCore 2 ↥H := by
      have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
      change QuotientGroup.mk' (CFSG.pCore 2 ↥H) ((x : ↥(B.subgroupOf H)) : ↥H) = 1 at h1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  obtain ⟨e₁⟩ := quotPCoreEquivOfSurjective ρ hsurj hker
  exact ⟨(quotPCoreSubgroupOfEquiv hBH).symm.trans e₁⟩

variable {T L I : Subgroup G} {n i : ℕ} {Vi V₀ : Subgroup G}

theorem barData_lOf (hF : Facts11) (hN : NatFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hU : IsVi T L I n i Vi) (hc : Hyp1111 T i Vi V₀) :
    BarData (modO2Image (Subgroup.normalizer (V₀ : Set G)) (LOf L Vi)) n := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := lOf_quot_SL2 hN h1102 h hc.i_cases hU
  obtain ⟨e₁⟩ := modO2Image_quotEquiv (hc.lOf_le hF h1102 h hU)
  exact barData_of_quot_SL2 h.one_lt hK (e₁.symm.trans e)

end CFSG.Quasithin.Vol2.Ch11.SecA
