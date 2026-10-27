module

public import CFSG.Quasithin.H13.A5Sit15g
public import CFSG.Quasithin.H13.A5SitSp4Card
public import CFSG.Quasithin.H13.A5SitSp4Norm
public import CFSG.Quasithin.H13.A5Sit15e

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.A5.Orth

namespace A5.Orth

theorem no_index_five {X Ω : Subgroup (MulAut (Multiplicative V4))} (hXS : X ≤ Spq)
    (hΩX : Ω ≤ X) (hΩO : Ω ≤ Oq) (hPΩ : P3 ≤ Ω) (hΩ : Nat.card Ω = 36)
    (hX : Nat.card X = 180) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite ↥X := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  set P' : Subgroup ↥X := P3.subgroupOf X with hP'def
  have hP'card : Nat.card P' = 9 := by
    rw [hP'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hPΩ.trans hΩX)).toEquiv, card_P3]
  have hP'3 : IsPGroup 3 P' := IsPGroup.of_card (n := 2) (by rw [hP'card]; norm_num)
  have hidxP : P'.index = 20 := by
    have h := Subgroup.card_mul_index P'
    rw [hP'card, hX] at h
    omega
  have hnot : ¬ 3 ∣ P'.index := by
    rw [hidxP]
    norm_num
  obtain ⟨Syl, hSyl⟩ : ∃ Syl : Sylow 3 ↥X, (Syl : Subgroup ↥X) = P' :=
    ⟨hP'3.toSylow hnot, IsPGroup.toSylow_coe _ _⟩
  have hSyl' : (Syl : Set ↥X) = (P' : Set ↥X) :=
    congrArg (fun K : Subgroup ↥X => (K : Set ↥X)) hSyl
  have hmod := card_sylow_modEq_one 3 ↥X
  rw [Sylow.card_eq_index_normalizer Syl, hSyl'] at hmod
  have hΩN : Ω.subgroupOf X ≤ Subgroup.normalizer (P' : Set ↥X) := by
    refine A5.le_normalizer_of_forall_conj_mem fun g hg p hp => ?_
    rw [Subgroup.mem_subgroupOf] at hg
    rw [hP'def, Subgroup.mem_subgroupOf] at hp ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine ⟨Oq.mul_mem (Oq.mul_mem (hΩO hg) hp.1) (Oq.inv_mem (hΩO hg)), ?_⟩
    rw [conj_pow, hp.2, mul_one, mul_inv_cancel]
  have hΩidx : (Ω.subgroupOf X).index = 5 := by
    have h := Subgroup.card_mul_index (Ω.subgroupOf X)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΩX).toEquiv, hΩ, hX] at h
    omega
  have hdvd : (Subgroup.normalizer (P' : Set ↥X)).index ∣ 5 :=
    hΩidx ▸ Subgroup.index_dvd_of_le hΩN
  have h1 : (Subgroup.normalizer (P' : Set ↥X)).index = 1 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hdvd with h | h
    · exact h
    · rw [h] at hmod
      exact absurd hmod (by decide)
  have hXO : X ≤ Oq := by
    intro g hg
    have hgN : (⟨g, hg⟩ : ↥X) ∈ Subgroup.normalizer (P' : Set ↥X) := by
      rw [Subgroup.index_eq_one.1 h1]
      exact Subgroup.mem_top _
    have hr : ∀ r ∈ P3, g * r * g⁻¹ ∈ Oq := by
      intro r hr
      have hrX : r ∈ X := (hPΩ.trans hΩX) hr
      have h := (Subgroup.mem_normalizer_iff.mp hgN ⟨r, hrX⟩).mp
        (by rw [hP'def, Subgroup.mem_subgroupOf]; exact hr)
      rw [hP'def, Subgroup.mem_subgroupOf] at h
      exact h.1
    exact mem_Oq_of_conj (hXS hg) (hr _ ofOC_r1_mem) (hr _ ofOC_r2_mem)
  have h72 : Nat.card X ∣ 72 := card_Oq ▸ Subgroup.card_dvd_of_le hXO
  rw [hX] at h72
  norm_num at h72

end A5.Orth

namespace A5SitPf15

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
  {S : A5Sit G T V V₁ V₃ L₁ H} {SY : A5SitY S L₁} (P : A5SitPf15 S SY)
include P

theorem P3_le_range : P3 ≤ P.Φ.range := by
  intro α hα
  have hc : P.ch ∈ P3 := ⟨P.ch_props.1, P.ch_props.2.2⟩
  obtain ⟨x, -, hx⟩ := P.centralizer_le_Φ hα.1 (P3_comm hα hc)
  exact ⟨x, hx⟩

theorem H_eq_of_U (h36 : Nat.card P.Φ.range = 36) {G₁ : Subgroup G}
    (hF1 : HypF91 T V S.L V₁ V₃ G₁) (hHG1 : H ≤ G₁)
    (hG1z : G₁ ≤ Subgroup.centralizer ({P.C.z} : Set G))
    (hQ1 : pCoreOf 2 G₁ = conjClosure V₃ H) : H = G₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUU1 : conjClosure V₃ H ≤ conjClosure V₃ G₁ := conjClosure_mono le_rfl hHG1
  have hU1Q1 : conjClosure V₃ G₁ ≤ pCoreOf 2 G₁ := hF1.conjClosure_Vp_le_pCoreOf
  have hU1 : conjClosure V₃ G₁ = conjClosure V₃ H := le_antisymm (hU1Q1.trans hQ1.le) hUU1
  have hQ1T : pCoreOf 2 G₁ ≤ T := pCoreOf_two_le_of_isSylowTwoOf hF1.sylow_H
  have hQ1Q : pCoreOf 2 G₁ ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 (hQ1T.trans S.T_le_H)
      (hHG1.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
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
  have hrange1 : Nat.card (P.C.act G₁ hG1N hG1z).range ≤ 72 := by
    rw [← card_Oq]
    have : Finite ↥Oq := finite_Oq
    exact Subgroup.card_le_of_le fun b ⟨x, hx⟩ => hx ▸ P.C.act_mem_Oq _ _ _ x
  have hQle : Nat.card (pCoreOf 2 G₁) ≤ Nat.card (pCoreOf 2 H) := Subgroup.card_le_of_le hQ1Q
  have hidx := Subgroup.card_mul_index (H.subgroupOf G₁)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHG1).toEquiv] at hidx
  have hodd : ¬ 2 ∣ (H.subgroupOf G₁).index := by
    intro h2
    apply hF1.sylow_H.2.2
    exact h2.trans (Subgroup.index_dvd_of_le fun x hx => S.T_le_H hx)
  generalize hn : (H.subgroupOf G₁).index = n at hidx hodd
  have hpos : 0 < Nat.card (pCoreOf 2 H) := Nat.card_pos
  have hle : Nat.card (pCoreOf 2 H) * (36 * n) ≤ Nat.card (pCoreOf 2 H) * 72 := by
    calc Nat.card (pCoreOf 2 H) * (36 * n) = Nat.card G₁ := by
          rw [← hidx, P.card_H, h36]
          ring
      _ = Nat.card (pCoreOf 2 G₁) * Nat.card (P.C.act G₁ hG1N hG1z).range := hcard1
      _ ≤ Nat.card (pCoreOf 2 H) * 72 := Nat.mul_le_mul hQle hrange1
  have hn2 : 36 * n ≤ 72 := Nat.le_of_mul_le_mul_left hle hpos
  have hn1 : n = 1 := by
    have hn0 : n ≠ 0 := by
      intro h0
      apply hodd
      rw [h0]
      exact dvd_zero 2
    omega
  have := Subgroup.index_eq_one.1 (hn.trans hn1)
  apply le_antisymm hHG1
  intro x hx
  have : (⟨x, hx⟩ : ↥G₁) ∈ H.subgroupOf G₁ := this ▸ Subgroup.mem_top _
  exact this

variable (hQ : Nat.card (pCoreOf 2 H) = 64)
include hQ

theorem H_eq_of_Q (h36 : Nat.card P.Φ.range = 36) {G₁ : Subgroup G}
    (hF1 : HypF91 T V S.L V₁ V₃ G₁) (hHG1 : H ≤ G₁)
    (hG1z : G₁ ≤ Subgroup.centralizer ({P.C.z} : Set G))
    (hQ1 : pCoreOf 2 G₁ = pCoreOf 2 H) : H = G₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG1N : G₁ ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hQ1 ▸ le_normalizer_pCoreOf 2 G₁
  have hQG1 : pCoreOf 2 H ≤ G₁ := hQ1 ▸ pCoreOf_le 2 G₁
  have h2 : IsPGroup 2 (P.actQ hQ G₁ hG1N).ker := P.isPGroup_ker_actQ hQ G₁ hG1N
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp (hG1z hx))
    (fun x hx hc => by
      have hxC : x ∈ G₁ ⊓ Subgroup.centralizer (pCoreOf 2 G₁ : Set G) := by
        refine ⟨hx, ?_⟩
        rw [hQ1]
        exact Subgroup.mem_centralizer_iff.2 fun q hq => (hc q hq).symm
      have h := hF1.charTwo_H hxC
      rwa [hQ1] at h)
  have hθφ : ∀ (x : ↥G₁) (q : ↥(pCoreOf 2 H)), P.actQ hQ G₁ hG1N x (P.thetaQ hQ q) =
      P.thetaQ hQ (Q8Coords.conjHom (hG1N x.2) q) := P.actQ_θ hQ G₁ hG1N
  have hSp : ∀ x, P.actQ hQ G₁ hG1N x ∈ Spq := P.actQ_mem_Spq hQ G₁ hG1N
  have hΦφ : ∀ h : ↥H, P.Φ h = P.actQ hQ G₁ hG1N ⟨h, hHG1 h.2⟩ := fun h => by
    rw [← P.actQ_H hQ h]
    rfl
  generalize P.actQ hQ G₁ hG1N = φ at h2 hθφ hSp hΦφ
  have hker : φ.ker = (pCoreOf 2 H).subgroupOf G₁ := by
    apply le_antisymm
    · have hK : φ.ker.map G₁.subtype ≤ pCoreOf 2 G₁ :=
        le_pCoreOf_of_le_normalizer 2 (Subgroup.map_subtype_le _)
          (A5.le_normalizer_of_forall_conj_mem fun g hg k hk => by
            obtain ⟨k', hk', rfl⟩ := hk
            exact ⟨⟨g, hg⟩ * k' * ⟨g, hg⟩⁻¹,
              (MonoidHom.normal_ker φ).conj_mem k' hk' _, rfl⟩)
          (h2.map _)
      intro x hx
      rw [Subgroup.mem_subgroupOf, ← hQ1]
      exact hK ⟨x, hx, rfl⟩
    · intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [MonoidHom.mem_ker]
      apply MulEquiv.ext
      intro w
      obtain ⟨p, rfl⟩ := P.thetaQ_surj hQ w
      rw [hθφ, MulAut.one_apply]
      have e : (Q8Coords.conjHom (hG1N x.2) p : ↥(pCoreOf 2 H)) =
          ⟨x, hx⟩ * p * (⟨x, hx⟩ : ↥(pCoreOf 2 H))⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      apply Multiplicative.toAdd.injective
      simp only [toAdd_mul, toAdd_inv]
      abel
  have hcard1 : Nat.card G₁ = Nat.card (pCoreOf 2 H) * Nat.card φ.range := by
    rw [← Subgroup.card_mul_index φ.ker, Subgroup.index_ker, hker]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQG1).toEquiv
  have hrangeS : φ.range ≤ Spq := by
    rintro _ ⟨x, rfl⟩
    exact hSp x
  have hΦle : P.Φ.range ≤ φ.range := by
    rintro _ ⟨h, rfl⟩
    exact ⟨⟨h, hHG1 h.2⟩, (hΦφ h).symm⟩
  have hidx := Subgroup.card_mul_index (H.subgroupOf G₁)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHG1).toEquiv] at hidx
  have hodd : ¬ 2 ∣ (H.subgroupOf G₁).index := by
    intro h2
    apply hF1.sylow_H.2.2
    exact h2.trans (Subgroup.index_dvd_of_le fun x hx => S.T_le_H hx)
  generalize hn : (H.subgroupOf G₁).index = n at hidx hodd
  have hpos : 0 < Nat.card (pCoreOf 2 H) := Nat.card_pos
  have hrange : Nat.card φ.range = 36 * n := by
    have e1 : Nat.card (pCoreOf 2 H) * Nat.card φ.range =
        Nat.card (pCoreOf 2 H) * (36 * n) := by
      rw [← hcard1, ← hidx, P.card_H, h36]
      ring
    exact Nat.eq_of_mul_eq_mul_left hpos e1
  have h720 : 36 * n ∣ 720 := by
    rw [← hrange, ← card_Spq]
    exact Subgroup.card_dvd_of_le hrangeS
  have hn20 : n ∣ 20 := by
    obtain ⟨k, hk⟩ := h720
    exact ⟨k, by nlinarith⟩
  have hn1 : n = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) hn20
    interval_cases n <;> try omega
    · exfalso
      exact no_index_five hrangeS (hΦle) (P.range_le) (P.P3_le_range) h36 (by rw [hrange])
  have := Subgroup.index_eq_one.1 (hn.trans hn1)
  apply le_antisymm hHG1
  intro x hx
  have : (⟨x, hx⟩ : ↥G₁) ∈ H.subgroupOf G₁ := this ▸ Subgroup.mem_top _
  exact this

end A5SitPf15

end CFSG.Quasithin.H13
