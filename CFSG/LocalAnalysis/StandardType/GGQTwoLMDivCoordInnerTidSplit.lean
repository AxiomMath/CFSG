module

import CFSG.LocalAnalysis.StandardType.GGQTwoLMMod
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerLift
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTker
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTor
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCCard

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.Assembly CFSG.StandardType.UCoord
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary Matrix

variable {G : Type} [Group G] [Finite G]

private lemma qTwoLMDivCoordInner_tidsplit_oneVec_order {m : ℕ} (h3 : 3 ∣ m) (hm : 0 < m) :
    orderOf (qTwoOneVec m h3) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply orderOf_eq_prime
  · apply Subtype.ext
    funext i
    simp only [Subgroup.coe_pow, Subgroup.coe_one, Pi.pow_apply, Pi.one_apply, qTwoOneVec]
    rw [← ofAdd_nsmul,
      show (3 : ℕ) • (1 : ZMod 3) = 0 by rw [nsmul_eq_mul, mul_one]; exact ZMod.natCast_self 3,
      ofAdd_zero]
  · intro h
    have h0 : Multiplicative.ofAdd (1 : ZMod 3) = 1 := by
      have h1 := congrFun (congrArg Subtype.val h) ⟨0, hm⟩
      simpa [qTwoOneVec] using h1
    exact one_ne_zero (ofAdd_eq_one.mp h0)

theorem qTwoLMDivCoordInner_tid_split {B Bs L : Subgroup G} {x : G} (hG : GGThmIHyp 3 B x L)
    (hBs : GGBstar 3 B Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {m : ℕ} (hm : 6 ≤ m)
    (h3 : 3 ∣ m)
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {L0 : Type} [Group L0]
    {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) {δ : ↥(sumZero m 3) →* Su F0 2 1 m}
    (hδ : QTwoDivTorus h3 δ) {τ : ↥(sumZero m 3) →* ↥L} (hτ : QTwoDivLift Bs L c π δ τ)
    (hcard : Nat.card Bs = 3 ^ (m - 1)) :
    ∀ b ∈ Bs, ∃ t : ↥L, (t : G) ∈ Bs ∧ ∃ k : ℕ, b = (t : G) * x ^ k := by
  classical
  have hS : LargeEvenSStar 3 B x L := hG.2.2.2.2.2.2.1
  obtain ⟨-, hxB, hx1, -, -⟩ := hS
  have hxBs : x ∈ Bs := hBs.1 hxB
  have hx3 : x ^ 3 = 1 := hBs.2.1.2 x hxBs
  have hxord : orderOf x = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hx3 hx1
  have hxBs_le : Subgroup.zpowers x ≤ Bs := Subgroup.zpowers_le.mpr hxBs
  let T : Subgroup G := Subgroup.map L.subtype τ.range
  have hTle : T ≤ Bs := by
    rintro g hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨y, hy, rfl⟩ := hg
    rw [MonoidHom.mem_range] at hy
    obtain ⟨f, rfl⟩ := hy
    exact hτ.mem f
  have hTcard : Nat.card T = Nat.card τ.range :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hTleL : T ≤ L := by
    rintro g hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨y, -, rfl⟩ := hg
    exact y.2
  by_cases h3dvd : 3 ∣ Nat.card (Subgroup.center ↥L)
  · intro b hb
    have hinj : Function.Injective τ :=
      (qTwoLMDivCoordInner_tker hG hN hm h3 hU hδ hτ).1 h3dvd
    have hcardBs : Nat.card T = Nat.card Bs := by
      rw [hTcard, (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm,
        qTwoLMFrameC_card_sumZero m]
      exact hcard.symm
    have hTeq : T = Bs := Subgroup.eq_of_le_of_card_ge hTle (le_of_eq hcardBs.symm)
    have hbT : b ∈ T := by rw [hTeq]; exact hb
    rw [Subgroup.mem_map] at hbT
    obtain ⟨u, hu, hbu⟩ := hbT
    rw [MonoidHom.mem_range] at hu
    obtain ⟨f, hf⟩ := hu
    refine ⟨τ f, hτ.mem f, 0, ?_⟩
    rw [pow_zero, mul_one, ← hbu, ← hf]
    rfl
  · intro b hb
    have hτker := (qTwoLMDivCoordInner_tker hG hN hm h3 hU hδ hτ).2.1 h3dvd
    have hker_eq : τ.ker = Subgroup.zpowers (qTwoOneVec m h3) := by
      ext f
      rw [MonoidHom.mem_ker, hτker f]
    have honevec : orderOf (qTwoOneVec m h3) = 3 :=
      qTwoLMDivCoordInner_tidsplit_oneVec_order h3 (by omega)
    have hker3 : Nat.card τ.ker = 3 := by
      rw [hker_eq, Nat.card_zpowers, honevec]
    have hp : 3 * 3 ^ (m - 2) = 3 ^ (m - 1) := by
      rw [mul_comm, ← pow_succ]
      congr 1
      omega
    have hp' : 3 ^ (m - 2) * 3 = 3 ^ (m - 1) := by
      rw [mul_comm]
      exact hp
    have hrange : Nat.card τ.range = 3 ^ (m - 2) := by
      have h := Subgroup.card_ker_mul_card_range τ
      rw [hker3, qTwoLMFrameC_card_sumZero m, ← hp] at h
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
    have hTcard2 : Nat.card T = 3 ^ (m - 2) := by
      rw [hTcard, hrange]
    have hxL : x ∉ L := by
      intro hxL
      have hxZ : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro l
        have hcomm := Subgroup.mem_centralizer_iff.mp (qTwoLMFrameC_le_centralizer hG l.2) x
          (Set.mem_singleton x)
        exact Subtype.ext hcomm.symm
      have hzord : orderOf (⟨⟨x, hxL⟩, hxZ⟩ : ↥(Subgroup.center ↥L)) = 3 := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hxord]
      exact h3dvd (hzord ▸ orderOf_dvd_natCard (⟨⟨x, hxL⟩, hxZ⟩ : ↥(Subgroup.center ↥L)))
    have hLbot : L ⊓ Subgroup.zpowers x = ⊥ := by
      have hcard_zp : Nat.card (Subgroup.zpowers x) = 3 := by
        rw [Nat.card_zpowers, hxord]
      have hdvd : Nat.card ↥(L ⊓ Subgroup.zpowers x) ∣ 3 := by
        rw [← hcard_zp]
        exact Subgroup.card_dvd_of_le inf_le_right
      have hne : Nat.card ↥(L ⊓ Subgroup.zpowers x) ≠ 3 := by
        intro h3c
        have heq : L ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3c, hcard_zp])
        have hle : Subgroup.zpowers x ≤ L := heq.symm.le.trans inf_le_left
        exact hxL (hle (Subgroup.mem_zpowers x))
      have h1 : Nat.card ↥(L ⊓ Subgroup.zpowers x) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact h
        · exact absurd h hne
      exact Subgroup.eq_bot_of_card_eq (L ⊓ Subgroup.zpowers x) h1
    have hdisj : T ⊓ Subgroup.zpowers x = ⊥ := by
      apply le_bot_iff.mp
      calc T ⊓ Subgroup.zpowers x ≤ L ⊓ Subgroup.zpowers x := inf_le_inf hTleL le_rfl
        _ = ⊥ := hLbot
    have hdisj' : Disjoint (T.subgroupOf Bs) ((Subgroup.zpowers x).subgroupOf Bs) := by
      rw [disjoint_iff]
      change T.comap Bs.subtype ⊓ (Subgroup.zpowers x).comap Bs.subtype = ⊥
      rw [← Subgroup.comap_inf, hdisj]
      ext z
      rw [Subgroup.mem_comap, Subgroup.mem_bot, Subgroup.mem_bot]
      exact ⟨fun h => Bs.subtype_injective (by rw [h, map_one]),
        fun h => by rw [h, map_one]⟩
    have hcardTsub : Nat.card (T.subgroupOf Bs) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv
    have hcardXsub : Nat.card ((Subgroup.zpowers x).subgroupOf Bs) =
        Nat.card (Subgroup.zpowers x) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hxBs_le).toEquiv
    have hcardφ : Nat.card (T.subgroupOf Bs) *
        Nat.card ((Subgroup.zpowers x).subgroupOf Bs) = Nat.card ↥Bs := by
      rw [hcardTsub, hcardXsub, Nat.card_zpowers, hxord, hTcard2, hp']
      exact hcard.symm
    have hcompl := Subgroup.isComplement'_of_card_mul_and_disjoint hcardφ hdisj'
    obtain ⟨⟨t', y'⟩, ht'y'⟩ := hcompl.2 ⟨b, hb⟩
    let tT : T := ⟨((t' : ↥Bs) : G), Subgroup.mem_subgroupOf.mp t'.2⟩
    let yX : Subgroup.zpowers x := ⟨((y' : ↥Bs) : G), Subgroup.mem_subgroupOf.mp y'.2⟩
    have ht'y'G : (tT : G) * (yX : G) = b := by
      have h := congrArg (fun z : ↥Bs => (z : G)) ht'y'
      simpa [tT, yX] using h
    have htT : (tT : G) ∈ T := tT.2
    rw [Subgroup.mem_map] at htT
    obtain ⟨u, hu, htu⟩ := htT
    rw [MonoidHom.mem_range] at hu
    obtain ⟨f, hf⟩ := hu
    have ht_eq : (tT : G) = ((τ f : ↥L) : G) := by
      rw [← htu, ← hf]
      rfl
    have hyX' : (yX : G) ∈ Subgroup.zpowers x := yX.2
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hyX'
    have hk : x ^ (z % (orderOf x : ℤ)).toNat = (yX : G) := by
      rw [← hz, ← zpow_natCast (a := x),
        Int.toNat_of_nonneg (Int.emod_nonneg z (by rw [hxord]; norm_num)),
        zpow_mod_orderOf]
    refine ⟨τ f, hτ.mem f, (z % (orderOf x : ℤ)).toNat, ?_⟩
    calc b = (tT : G) * (yX : G) := ht'y'G.symm
      _ = ((τ f : ↥L) : G) * x ^ (z % (orderOf x : ℤ)).toNat := by rw [ht_eq, ← hk]

end CFSG.StandardType.QTwo

end
