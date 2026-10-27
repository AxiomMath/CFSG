module

public import CFSG.CGT.Timmesfeld75.L2Sylow
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.H13.L32NSp4Over
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Basic
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section SL2

variable {F : Type} [Field F]

theorem sl2_normalizer_le_conj_borel {V : Subgroup SL(2, F)} {c : SL(2, F)}
    (hV : V ≤ conjSubgroup c (utri F)) (hne : V ≠ ⊥) :
    Subgroup.normalizer (V : Set SL(2, F)) ≤ conjSubgroup c (borel F) := by
  obtain ⟨v, hvV, hv1⟩ := (Subgroup.bot_or_exists_ne_one V).resolve_left hne
  have hv' : c⁻¹ * v * c ∈ utri F := mem_conjSubgroup.1 (hV hvV)
  obtain ⟨s, hs⟩ := mem_utri_iff.1 hv'
  have hs0 : s ≠ 0 := fun h0 => hv1 (by
    have h1 : c⁻¹ * v * c = 1 := by rw [hs, h0, utriElt_zero]
    calc v = c * (c⁻¹ * v * c) * c⁻¹ := by group
      _ = 1 := by rw [h1]; group)
  intro g hg
  rw [mem_conjSubgroup]
  have h1 : g * v * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hg v).1 hvV
  have h2 : c⁻¹ * (g * v * g⁻¹) * c ∈ utri F := mem_conjSubgroup.1 (hV h1)
  have e : c⁻¹ * (g * v * g⁻¹) * c = (c⁻¹ * g * c) * utriElt s * (c⁻¹ * g * c)⁻¹ := by
    rw [← hs]
    group
  rw [e] at h2
  have h10 : ((c⁻¹ * g * c) * utriElt s * (c⁻¹ * g * c)⁻¹) 1 0 = 0 := h2.1
  rw [conj_utriElt_apply_10] at h10
  have h3 : (c⁻¹ * g * c) 1 0 ^ 2 * s = 0 := by linear_combination (-1) * h10
  have h4 : (c⁻¹ * g * c) 1 0 ^ 2 = 0 := (mul_eq_zero.1 h3).resolve_right hs0
  exact (pow_eq_zero_iff two_ne_zero).1 h4

end SL2

section SL2Fin

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem sl2_two_subgroups (h4 : 4 ≤ Nat.card F) {U U' : Subgroup SL(2, F)}
    (hU : IsPGroup 2 U) (hU' : IsPGroup 2 U') (hUne : U ≠ ⊥) (hU'ne : U' ≠ ⊥)
    (hsup : U ⊔ U' = ⊤) :
    U ⊓ Subgroup.normalizer (U' : Set SL(2, F)) = ⊥ ∧
      Nat.card ↥(Subgroup.normalizer (U : Set SL(2, F))) ≤ Nat.card F * (Nat.card F - 1) := by
  classical
  obtain ⟨P, hUP⟩ := hU.exists_le_sylow
  obtain ⟨P', hU'P'⟩ := hU'.exists_le_sylow
  obtain ⟨c, hc⟩ := exists_conjSubgroup_utri_eq_of_sylow P
  obtain ⟨c', hc'⟩ := exists_conjSubgroup_utri_eq_of_sylow P'
  have hUc : U ≤ conjSubgroup c (utri F) := hc ▸ hUP
  have hU'c : U' ≤ conjSubgroup c' (utri F) := hc' ▸ hU'P'
  have hPP : conjSubgroup c (utri F) ≠ conjSubgroup c' (utri F) := by
    intro heq
    have hle : U ⊔ U' ≤ conjSubgroup c (utri F) := sup_le hUc (heq ▸ hU'c)
    rw [hsup] at hle
    have h1 : Nat.card (⊤ : Subgroup SL(2, F)) ≤ Nat.card (conjSubgroup c (utri F)) :=
      Subgroup.card_le_of_le hle
    rw [Subgroup.card_top, card_sl2, card_conjSubgroup, card_utri] at h1
    have h5 : 3 ≤ Nat.card F ^ 2 - 1 := by
      have : 16 ≤ Nat.card F ^ 2 := by nlinarith
      omega
    have h6 : Nat.card F * 3 ≤ Nat.card F * (Nat.card F ^ 2 - 1) := Nat.mul_le_mul_left _ h5
    omega
  have hcc : c'⁻¹ * c ∉ borel F := by
    intro hb
    apply hPP
    exact (conjSubgroup_eq_conjSubgroup_iff.2 (by rwa [normalizer_utri])).symm
  have hN' : Subgroup.normalizer (U' : Set SL(2, F)) ≤ conjSubgroup c' (borel F) :=
    sl2_normalizer_le_conj_borel hU'c hU'ne
  have hN : Subgroup.normalizer (U : Set SL(2, F)) ≤ conjSubgroup c (borel F) :=
    sl2_normalizer_le_conj_borel hUc hUne
  refine ⟨?_, ?_⟩
  · rw [eq_bot_iff]
    rintro y ⟨hyU, hyN⟩
    have h1 : y ∈ conjSubgroup c (utri F) := hUc hyU
    have h2 : y ∈ conjSubgroup c' (borel F) := hN' hyN
    have h3 : c'⁻¹ * y * c' ∈ borel F ⊓ conjSubgroup (c'⁻¹ * c) (utri F) := by
      refine ⟨mem_conjSubgroup.1 h2, mem_conjSubgroup.2 ?_⟩
      have e : (c'⁻¹ * c)⁻¹ * (c'⁻¹ * y * c') * (c'⁻¹ * c) = c⁻¹ * y * c := by group
      rw [e]
      exact mem_conjSubgroup.1 h1
    rw [inf_borel_conj_utri_eq_bot hcc, Subgroup.mem_bot] at h3
    rw [Subgroup.mem_bot]
    calc y = c' * (c'⁻¹ * y * c') * c'⁻¹ := by group
      _ = 1 := by rw [h3]; group
  · have := Subgroup.card_le_of_le hN
    rwa [card_conjSubgroup, card_borel] at this

end SL2Fin

section Cover

theorem card_le_of_cover {Γ : Type} [Group Γ] [Finite Γ] (N U : Subgroup Γ) (w : Γ)
    (hcov : ∀ y : Γ, y ∈ N ∨ ∃ ε ∈ U, (ε * w)⁻¹ * y ∈ N) :
    Nat.card Γ ≤ Nat.card N * (1 + Nat.card U) := by
  classical
  let f : ↥N ⊕ (↥U × ↥N) → Γ :=
    Sum.elim (fun n => (n : Γ)) (fun p => (p.1 : Γ) * w * (p.2 : Γ))
  have hf : Function.Surjective f := by
    intro y
    rcases hcov y with hy | ⟨ε, hε, hn⟩
    · exact ⟨Sum.inl ⟨y, hy⟩, rfl⟩
    · refine ⟨Sum.inr (⟨ε, hε⟩, ⟨(ε * w)⁻¹ * y, hn⟩), ?_⟩
      show ε * w * ((ε * w)⁻¹ * y) = y
      group
  have := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_sum, Nat.card_prod] at this
  nlinarith

end Cover

section Bridge

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]

theorem map_mem_normalizer_of_mem_normalizer {Γ : Type} [Group Γ] {X T : Subgroup G}
    (π : ↥X →* Γ) (hT : T ≤ X) {g : G} (hg : g ∈ X)
    (hgN : g ∈ Subgroup.normalizer (T : Set G)) :
    π ⟨g, hg⟩ ∈ Subgroup.normalizer (((T.subgroupOf X).map π : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · rintro ⟨t, ht, rfl⟩
    have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
    refine ⟨⟨g, hg⟩ * t * ⟨g, hg⟩⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
    exact (Subgroup.mem_normalizer_iff.mp hgN _).mp htT
  · rintro ⟨t, ht, hte⟩
    have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
    refine ⟨⟨g, hg⟩⁻¹ * t * ⟨g, hg⟩, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) _).mp htT
      simpa using this
    · have : π ⟨g, hg⟩ * u * (π ⟨g, hg⟩)⁻¹ = π t := hte.symm
      calc π (⟨g, hg⟩⁻¹ * t * ⟨g, hg⟩) = (π ⟨g, hg⟩)⁻¹ * π t * π ⟨g, hg⟩ := by simp
        _ = u := by rw [← this]; group

theorem odd_sq_sub_one_of_two_pow' {q : ℕ} (hq : ∃ e : ℕ, q = 2 ^ e) (h4 : 4 ≤ q) :
    Odd (q ^ 2 - 1) := by
  have h2 : 2 ∣ q := by
    obtain ⟨e, rfl⟩ := hq
    have he : e ≠ 0 := by
      rintro rfl
      simp at h4
    exact dvd_pow_self 2 he
  obtain ⟨c, rfl⟩ := h2
  have hc1 : 1 ≤ c := by omega
  have e : (2 * c) ^ 2 = 4 * (c * c) := by ring
  rw [e]
  have ht : 1 ≤ c * c := Nat.mul_pos hc1 hc1
  generalize c * c = u at ht
  exact ⟨2 * u - 1, by omega⟩

theorem arith_sylow {q N u : ℕ} (h4 : 4 ≤ q) (hN : N ≤ q * (q - 1))
    (h : q * (q ^ 2 - 1) ≤ N * (1 + u)) : q ≤ u := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  have e1 : (m + 1) ^ 2 - 1 = m * (m + 2) := by
    have : (m + 1) ^ 2 = m * (m + 2) + 1 := by ring
    omega
  have e2 : m + 1 - 1 = m := by omega
  rw [e1] at h
  rw [e2] at hN
  by_contra hlt
  push Not at hlt
  have h1 : N * (1 + u) ≤ (m + 1) * m * (m + 1) := by
    calc N * (1 + u) ≤ ((m + 1) * m) * (1 + u) := Nat.mul_le_mul_right _ hN
      _ ≤ ((m + 1) * m) * (m + 1) := Nat.mul_le_mul_left _ (by omega)
  have h2 : (m + 1) * (m * (m + 2)) ≤ (m + 1) * m * (m + 1) := h.trans h1
  nlinarith

theorem sl2_bridge {L L' F X : Subgroup G} (hXdef : L ⊔ L' = X) (h4 : 4 ≤ Nat.card K)
    (hq2 : ∃ e : ℕ, Nat.card K = 2 ^ e) (hL : IsPGroup 2 ↥L) (hL' : IsPGroup 2 ↥L')
    (π : ↥X →* SL(2, K)) (hsurj : Function.Surjective π)
    (hker : ∀ x : ↥X, π x = 1 ↔ (x : G) ∈ F) {w : G} (hw : w ∈ X)
    (hcov : ∀ y ∈ X, y ∈ Subgroup.normalizer (L : Set G) ∨
      ∃ ε ∈ L, (ε * w)⁻¹ * y ∈ Subgroup.normalizer (L : Set G)) :
    (∀ y ∈ L, y ∈ Subgroup.normalizer (L' : Set G) → y ∈ F) ∧
      Nat.card K ≤ F.relIndex L := by
  classical
  have hLX : L ≤ X := hXdef ▸ le_sup_left
  have hL'X : L' ≤ X := hXdef ▸ le_sup_right
  set U : Subgroup SL(2, K) := (L.subgroupOf X).map π with hU
  set U' : Subgroup SL(2, K) := (L'.subgroupOf X).map π with hU'
  have hU2 : IsPGroup 2 ↥U := (hL.of_equiv (Subgroup.subgroupOfEquivOfLe hLX).symm).map π
  have hU'2 : IsPGroup 2 ↥U' := (hL'.of_equiv (Subgroup.subgroupOfEquivOfLe hL'X).symm).map π
  have hsup : U ⊔ U' = ⊤ := by
    have h1 : L.subgroupOf X ⊔ L'.subgroupOf X = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hLX hL'X, hXdef]
      exact Subgroup.subgroupOf_self _
    rw [hU, hU', ← Subgroup.map_sup, h1, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr hsurj
  have hnot2 : ¬ IsPGroup 2 ↥(⊤ : Subgroup SL(2, K)) := by
    intro h2
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
    rw [Subgroup.card_top, card_sl2] at hk
    have hodd := odd_sq_sub_one_of_two_pow' hq2 h4
    have hdvd : (Nat.card K ^ 2 - 1) ∣ 2 ^ k := hk ▸ Dvd.intro_left _ rfl
    have hcop : Nat.Coprime (Nat.card K ^ 2 - 1) 2 := hodd.coprime_two_right
    have h1 : Nat.card K ^ 2 - 1 = 1 := Nat.Coprime.eq_one_of_dvd (hcop.pow_right k) hdvd
    have : 16 ≤ Nat.card K ^ 2 := by nlinarith
    omega
  have hUne : U ≠ ⊥ := by
    intro h0
    rw [h0, bot_sup_eq] at hsup
    exact hnot2 (hsup ▸ hU'2)
  have hU'ne : U' ≠ ⊥ := by
    intro h0
    rw [h0, sup_bot_eq] at hsup
    exact hnot2 (hsup ▸ hU2)
  obtain ⟨hinf, hcardN⟩ := sl2_two_subgroups h4 hU2 hU'2 hUne hU'ne hsup
  refine ⟨?_, ?_⟩
  · intro y hy hyN
    have hyX : y ∈ X := hLX hy
    have h1 : π ⟨y, hyX⟩ ∈ U := ⟨⟨y, hyX⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    have h2 : π ⟨y, hyX⟩ ∈ Subgroup.normalizer (U' : Set SL(2, K)) :=
      map_mem_normalizer_of_mem_normalizer π hL'X hyX hyN
    have h3 : π ⟨y, hyX⟩ ∈ U ⊓ Subgroup.normalizer (U' : Set SL(2, K)) := ⟨h1, h2⟩
    rw [hinf, Subgroup.mem_bot] at h3
    exact (hker ⟨y, hyX⟩).mp h3
  · have hUcard : Nat.card U = F.relIndex L := by
      rw [hU, ← Subgroup.relIndex_ker (K := L.subgroupOf X) π]
      have hkerπ : π.ker = F.subgroupOf X := by
        ext x
        rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
      rw [hkerπ, Subgroup.relIndex_subgroupOf hLX]
    have hcovSL : ∀ s : SL(2, K), s ∈ Subgroup.normalizer (U : Set SL(2, K)) ∨
        ∃ ε ∈ U, (ε * π ⟨w, hw⟩)⁻¹ * s ∈ Subgroup.normalizer (U : Set SL(2, K)) := by
      intro s
      obtain ⟨y, rfl⟩ := hsurj s
      rcases hcov (y : G) y.2 with hy | ⟨ε, hε, hn⟩
      · left
        exact map_mem_normalizer_of_mem_normalizer π hLX y.2 hy
      · right
        refine ⟨π ⟨ε, hLX hε⟩, ⟨⟨ε, hLX hε⟩, Subgroup.mem_subgroupOf.mpr hε, rfl⟩, ?_⟩
        have hmem : (ε * w)⁻¹ * (y : G) ∈ X :=
          X.mul_mem (X.inv_mem (X.mul_mem (hLX hε) hw)) y.2
        have := map_mem_normalizer_of_mem_normalizer π hLX hmem hn
        have e : π ⟨(ε * w)⁻¹ * (y : G), hmem⟩ =
            (π ⟨ε, hLX hε⟩ * π ⟨w, hw⟩)⁻¹ * π y := by
          rw [← map_mul, ← map_inv, ← map_mul]
          rfl
        rw [e] at this
        exact this
    have hcard := card_le_of_cover _ U (π ⟨w, hw⟩) hcovSL
    rw [card_sl2] at hcard
    rw [← hUcard]
    exact arith_sylow h4 hcardN hcard

end Bridge

end CFSG.RankThree.GF2n.Stroth80
