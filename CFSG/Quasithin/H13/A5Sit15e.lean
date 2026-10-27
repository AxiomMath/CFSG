module

public import CFSG.Quasithin.H13.A5Sit15c

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.A5.Orth

namespace A5.Orth

@[expose] def NotNormalAt (c : OC) : Prop := Ord3 c.cols → ∃ a : OC, ¬ NormC c.cols a.cols

instance (c : OC) : Decidable (NotNormalAt c) := by unfold NotNormalAt; infer_instance

theorem notNormalAt_all : ∀ c : OC, NotNormalAt c := by
  decide +kernel

theorem exists_not_normC {c : MulAut (Multiplicative V4)} (hc : c ∈ Oq)
    (h3 : c ≠ 1 ∧ c ^ 3 = 1) : ∃ a ∈ Oq, ¬ (a * c = c * a ∨ a * c = c * c * a) := by
  obtain ⟨a, ha⟩ := notNormalAt_all (toOC ⟨c, hc⟩)
    (by rw [toOC_mk_cols, ord3_colsOf_iff]; exact h3)
  obtain ⟨α, rfl⟩ := toOC_surjective a
  refine ⟨α, α.2, fun h => ha ?_⟩
  rw [toOC_mk_cols, toOC_cols, normC_colsOf_iff]
  exact h

theorem finite_Oq : Finite ↥Oq := Nat.finite_of_card_ne_zero (by rw [card_Oq]; norm_num)

end A5.Orth

namespace A5Sit

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
  (S : A5Sit G T V V₁ V₃ L₁ H)
include S

theorem inf_Q_eq : V ⊓ pCoreOf 2 H = V₃ := by
  have hle : V₃ ≤ V ⊓ pCoreOf 2 H := le_inf S.V3_le_V ((le_conjClosure V₃ H).trans S.U_le_Q)
  have h := Subgroup.relIndex_mul_relIndex V₃ (V ⊓ pCoreOf 2 H) V hle inf_le_left
  rw [S.relIndex_V3] at h
  have h1 : (V ⊓ pCoreOf 2 H).relIndex V ≠ 1 := fun h1 =>
    S.not_V_le ((Subgroup.relIndex_eq_one.1 h1).trans inf_le_right)
  have h2 : V₃.relIndex (V ⊓ pCoreOf 2 H) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 (Dvd.intro_left _ h) with h3 | h3
    · exact absurd h3 h1
    · rw [h3] at h
      omega
  exact le_antisymm (Subgroup.relIndex_eq_one.1 h2) hle

end A5Sit

namespace A5SitPf15

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
  {S : A5Sit G T V V₁ V₃ L₁ H} {SY : A5SitY S L₁} (P : A5SitPf15 S SY)
include P

theorem range_le : P.Φ.range ≤ Oq := by
  rintro _ ⟨x, rfl⟩
  exact P.Φ_mem x

theorem range_ne_Oq : P.Φ.range ≠ Oq := by
  intro h
  obtain ⟨a, haO, hna⟩ := exists_not_normC P.ch_props.1 ⟨P.ch_props.2.1, P.ch_props.2.2⟩
  rw [← h] at haO
  obtain ⟨x, rfl⟩ := haO
  exact hna (P.Φ_normalizes x)

theorem card_range : Nat.card P.Φ.range = 18 ∨ Nat.card P.Φ.range = 36 := by
  have : Finite ↥Oq := finite_Oq
  have h72 : Nat.card P.Φ.range ∣ 72 := by
    rw [← card_Oq]
    exact Subgroup.card_dvd_of_le P.range_le
  have hne : Nat.card P.Φ.range ≠ 72 := fun h =>
    P.range_ne_Oq (Subgroup.eq_of_le_of_card_ge P.range_le (by rw [card_Oq, h]))
  obtain ⟨k, hk⟩ := P.dvd_card_range
  obtain ⟨m, hm⟩ := h72
  rw [hk] at hm hne ⊢
  have hk4 : k ∣ 4 := ⟨m, by nlinarith⟩
  have hle := Nat.le_of_dvd (by norm_num) hk4
  interval_cases k <;> omega

theorem finite_range : Finite ↥P.Φ.range :=
  Finite.of_surjective P.Φ.rangeRestrict P.Φ.rangeRestrict_surjective

theorem card_range_eq {R : Subgroup G} (hRH : R ≤ H) (hR : IsPGroup 2 R) {a b : G}
    (ha : a ∈ R) (hb : b ∈ R) (ha1 : a ∉ pCoreOf 2 H) (hb1 : b ∉ pCoreOf 2 H)
    (hab : a * b⁻¹ ∉ pCoreOf 2 H) : Nat.card P.Φ.range = 36 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥P.Φ.range := P.finite_range
  rcases P.card_range with h | h
  · exfalso
    set X : Subgroup ↥P.Φ.range := (R.subgroupOf H).map P.Φ.rangeRestrict with hXdef
    have hX : IsPGroup 2 X := (hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRH).symm).map _
    obtain ⟨n, hn⟩ := hX.exists_card_eq
    have hdvd : Nat.card X ∣ 18 := by
      rw [← h]
      exact Subgroup.card_subgroup_dvd_card X
    have hmem : ∀ x (hx : x ∈ R), P.Φ.rangeRestrict ⟨x, hRH hx⟩ ∈ X := fun x hx =>
      ⟨⟨x, hRH hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    have hne1 : ∀ x (hx : x ∈ R), x ∉ pCoreOf 2 H →
        P.Φ.rangeRestrict ⟨x, hRH hx⟩ ≠ 1 := by
      intro x hx hxQ h1
      apply hxQ
      have : P.Φ ⟨x, hRH hx⟩ = 1 := congrArg Subtype.val h1
      exact (P.Φ_eq_one_iff _).1 this
    have hneab : P.Φ.rangeRestrict ⟨a, hRH ha⟩ ≠ P.Φ.rangeRestrict ⟨b, hRH hb⟩ := by
      intro h1
      apply hab
      have : P.Φ ⟨a, hRH ha⟩ = P.Φ ⟨b, hRH hb⟩ := congrArg Subtype.val h1
      exact (P.Φ_eq_iff _ _).1 this
    have hsub : ({1, P.Φ.rangeRestrict ⟨a, hRH ha⟩, P.Φ.rangeRestrict ⟨b, hRH hb⟩} :
        Set ↥P.Φ.range) ⊆ (X : Set ↥P.Φ.range) := by
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact X.one_mem
      · exact hmem a ha
      · exact hmem b hb
    have h3 : 3 ≤ Nat.card X := by
      calc 3 = Nat.card ({1, P.Φ.rangeRestrict ⟨a, hRH ha⟩,
              P.Φ.rangeRestrict ⟨b, hRH hb⟩} : Set ↥P.Φ.range) := by
            rw [Nat.card_coe_set_eq, Set.ncard_eq_three.2 ⟨_, _, _,
              (hne1 a ha ha1).symm, (hne1 b hb hb1).symm, hneab, rfl⟩]
        _ ≤ Nat.card (X : Set ↥P.Φ.range) := Nat.card_mono (Set.toFinite _) hsub
        _ = Nat.card X := rfl
    rw [hn] at h3 hdvd
    have hn2 : 2 ≤ n := by
      by_contra h2
      have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at this
      omega
    have := (Nat.pow_dvd_pow 2 hn2).trans hdvd
    norm_num at this
  · exact h

theorem card_H : Nat.card H = Nat.card (pCoreOf 2 H) * Nat.card P.Φ.range := by
  have hkerH : P.Φ.ker = (pCoreOf 2 H).subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, P.Φ_eq_one_iff]
  rw [← Subgroup.card_mul_index ((pCoreOf 2 H).subgroupOf H), ← hkerH,
    Subgroup.index_ker, hkerH]
  congr 1
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 H)).toEquiv

theorem H_eq_of (hQU : pCoreOf 2 H = conjClosure V₃ H) {G₁ : Subgroup G}
    (hF1 : HypF91 T V S.L V₁ V₃ G₁) (hHG1 : H ≤ G₁)
    (hG1z : G₁ ≤ Subgroup.centralizer ({P.C.z} : Set G)) : H = G₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ1T : pCoreOf 2 G₁ ≤ T := pCoreOf_two_le_of_isSylowTwoOf hF1.sylow_H
  have hQ1Q : pCoreOf 2 G₁ ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 (hQ1T.trans S.T_le_H)
      (hHG1.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have hUU1 : conjClosure V₃ H ≤ conjClosure V₃ G₁ := conjClosure_mono le_rfl hHG1
  have hU1Q1 : conjClosure V₃ G₁ ≤ pCoreOf 2 G₁ := hF1.conjClosure_Vp_le_pCoreOf
  have hQ1 : pCoreOf 2 G₁ = conjClosure V₃ H :=
    le_antisymm (hQ1Q.trans hQU.le) (hUU1.trans hU1Q1)
  have hU1 : conjClosure V₃ G₁ = conjClosure V₃ H :=
    le_antisymm (hU1Q1.trans hQ1.le) hUU1
  have hG1N : G₁ ≤ Subgroup.normalizer (conjClosure V₃ H : Set G) :=
    hQ1 ▸ le_normalizer_pCoreOf 2 G₁
  have hker1 : (P.C.act G₁ hG1N hG1z).ker = (pCoreOf 2 G₁).subgroupOf G₁ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Q8Coords.act_eq_one_iff, hF1.F92_3.1, hU1,
      mem_centralizerMod]
    constructor
    · intro h
      refine ⟨x.2, hF1.H_normalizes_V₁ x.2, fun u hu => ?_⟩
      rw [P.Cz]
      exact h u hu
    · intro h u hu
      have := h.2.2 u hu
      rwa [P.Cz] at this
  have hcard1 : Nat.card G₁ =
      Nat.card (pCoreOf 2 G₁) * Nat.card (P.C.act G₁ hG1N hG1z).range := by
    rw [← Subgroup.card_mul_index ((pCoreOf 2 G₁).subgroupOf G₁), ← hker1,
      Subgroup.index_ker, hker1]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 G₁)).toEquiv
  have hrange1 : Nat.card (P.C.act G₁ hG1N hG1z).range ∣ 72 := by
    rw [← card_Oq]
    exact Subgroup.card_dvd_of_le fun b ⟨x, hx⟩ => hx ▸ P.C.act_mem_Oq _ _ _ x
  have hQeq : Nat.card (pCoreOf 2 G₁) = Nat.card (pCoreOf 2 H) := by rw [hQ1, hQU]
  have hpos : 0 < Nat.card (pCoreOf 2 H) := Nat.card_pos
  obtain ⟨k, hk⟩ := P.dvd_card_range
  obtain ⟨m, hm⟩ := hrange1
  have hidx := Subgroup.card_mul_index (H.subgroupOf G₁)
  have hHcard : Nat.card ↥(H.subgroupOf G₁) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHG1).toEquiv
  rw [hHcard] at hidx
  have hodd : ¬ 2 ∣ (H.subgroupOf G₁).index := by
    intro h2
    apply hF1.sylow_H.2.2
    exact h2.trans (Subgroup.index_dvd_of_le fun x hx => S.T_le_H hx)
  generalize hn : (H.subgroupOf G₁).index = n at hidx hodd
  have h4 : n ∣ 4 := by
    have e1 : Nat.card (pCoreOf 2 H) * (18 * k * n * m) = Nat.card (pCoreOf 2 H) * 72 := by
      have := hcard1
      rw [hQeq, ← hidx, P.card_H, hk] at this
      calc Nat.card (pCoreOf 2 H) * (18 * k * n * m)
          = Nat.card (pCoreOf 2 H) * (18 * k) * n * m := by ring
        _ = Nat.card (pCoreOf 2 H) * Nat.card ↥(P.C.act G₁ hG1N hG1z).range * m := by
          rw [this]
        _ = Nat.card (pCoreOf 2 H) * 72 := by rw [hm]; ring
    have e2 : 18 * k * n * m = 72 := Nat.eq_of_mul_eq_mul_left hpos e1
    exact ⟨k * m, by nlinarith [e2]⟩
  have hn1 : n = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) h4
    interval_cases n <;> omega
  have := Subgroup.index_eq_one.1 (hn.trans hn1)
  apply le_antisymm hHG1
  intro x hx
  have : (⟨x, hx⟩ : ↥G₁) ∈ H.subgroupOf G₁ := this ▸ Subgroup.mem_top _
  exact this

end A5SitPf15

end CFSG.Quasithin.H13
