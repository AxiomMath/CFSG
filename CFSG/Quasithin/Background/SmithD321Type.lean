module

public import CFSG.Quasithin.Vol2.Ch10SecAShapeB42
public import CFSG.Quasithin.Background.F918J0
import CFSG.Quasithin.Background.B4ModelsWitness
public import CFSG.Quasithin.Background.B4ModelsApi

public section

namespace CFSG.Quasithin.SmithD321

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2.Ch10.SecA

theorem card_eq_of_realizesVia_nat {V : Type} [CommGroup V] {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] [Finite K] {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    {H : Subgroup (MulAut V)} {π : ↥Γ →* ↥H} (h : (FFModel.nat Γ).RealizesVia H ⊤ ⊥ π) :
    Nat.card V = Nat.card K ^ Fintype.card ι := by
  rw [card_eq_of_realizesVia_top h]
  change Nat.card (↥(⊤ : Subgroup (Multiplicative (ι → K))) ⧸
    (⊥ : Subgroup (Multiplicative (ι → K))).subgroupOf ⊤) = _
  rw [card_top_quot_bot, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    Nat.card_eq_fintype_card (α := ι)]

theorem card_altDn_mod_of_odd {n : ℕ} (hn : 1 ≤ n) (ho : ¬ Even n) :
    Nat.card (FFModel.altDn n).Mod = 2 ^ (n - 1) := by
  have h := Explicit.card_dn_sec hn .alternating
  rw [ite_eq_right ho] at h
  exact h

theorem card_symDn_mod_of_odd {n : ℕ} (hn : 1 ≤ n) (ho : ¬ Even n) :
    Nat.card (FFModel.symDn n).Mod = 2 ^ (n - 1) := by
  have h := Explicit.card_dn_sec hn .symmetric
  rw [ite_eq_right ho] at h
  exact h

theorem eq_of_two_pow_mul_eq_of_not_dvd {a b x y : ℕ} (hx : ¬ 2 ∣ x) (hy : ¬ 2 ∣ y)
    (h : 2 ^ a * x = 2 ^ b * y) : a = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ dvd_zero 2)
  have hy0 : y ≠ 0 := fun h0 => hy (h0 ▸ dvd_zero 2)
  have h1 := congrArg (padicValNat 2) h
  rwa [padicValNat.mul (pow_ne_zero _ two_ne_zero) hx0,
    padicValNat.mul (pow_ne_zero _ two_ne_zero) hy0, padicValNat.prime_pow,
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hx, padicValNat.eq_zero_of_not_dvd hy,
    add_zero, add_zero] at h1

theorem isPSL_three_two_of_mulEquiv {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 1) (e : X ≃* ↥(StatedSL 3 K)) : IsPSL 3 2 1 X := by
  have hunits : ∀ c : Kˣ, c = 1 := by
    intro c
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : K)).1 (by simpa using hK)
    exact Units.ext ((hy (c : K) c.ne_zero).trans (hy 1 one_ne_zero).symm)
  have hbot : (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨c, hc⟩ := hx
    rw [hunits c, map_one] at hc
    exact Subgroup.mem_bot.2 (Subtype.ext hc.symm)
  exact ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, K, inferInstance,
    inferInstance, hK, ⟨e.trans (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hbot.symm))⟩⟩

section Swap

theorem eq_swap_of_isSwap {α : Type*} [DecidableEq α] {σ : Equiv.Perm α} (hσ : σ.IsSwap)
    {x : α} (hx : σ x ≠ x) : σ = Equiv.swap x (σ x) := by
  obtain ⟨a, b, -, rfl⟩ := hσ
  by_cases hxa : x = a
  · subst hxa
    simp
  · by_cases hxb : x = b
    · subst hxb
      simp [Equiv.swap_comm]
    · exact absurd (Equiv.swap_apply_of_ne_of_ne hxa hxb) hx

theorem disjoint_of_commute_isSwap {α : Type*} [DecidableEq α] {σ τ : Equiv.Perm α}
    (hσ : σ.IsSwap) (hτ : τ.IsSwap) (hne : σ ≠ τ) (hc : Commute σ τ) : σ.Disjoint τ := by
  intro x
  by_contra hx
  rw [not_or] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have e1 := eq_swap_of_isSwap hσ hx1
  have e2 := eq_swap_of_isSwap hτ hx2
  have hyz : σ x ≠ τ x := fun h => hne (by rw [e1, e2, h])
  have h1 := congrArg (fun π : Equiv.Perm α => π x) hc.eq
  simp only [Equiv.Perm.mul_apply] at h1
  have a1 : σ (τ x) = τ x := by
    rw [e1]
    exact Equiv.swap_apply_of_ne_of_ne hx2 (Ne.symm hyz)
  have a2 : τ (σ x) = σ x := by
    rw [e2]
    exact Equiv.swap_apply_of_ne_of_ne hx1 hyz
  rw [a1, a2] at h1
  exact hyz h1.symm

theorem not_three_commuting_isSwap {s t u : Equiv.Perm (Fin 5)} (hs : s.IsSwap) (ht : t.IsSwap)
    (hu : u.IsSwap) (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) (cst : Commute s t)
    (csu : Commute s u) (ctu : Commute t u) : False := by
  have d1 := Equiv.Perm.disjoint_iff_disjoint_support.1 (disjoint_of_commute_isSwap hs ht hst cst)
  have d2 := Equiv.Perm.disjoint_iff_disjoint_support.1 (disjoint_of_commute_isSwap hs hu hsu csu)
  have d3 := Equiv.Perm.disjoint_iff_disjoint_support.1 (disjoint_of_commute_isSwap ht hu htu ctu)
  have h := Finset.card_le_univ (s.support ∪ t.support ∪ u.support)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨d2, d3⟩),
    Finset.card_union_of_disjoint d1, Equiv.Perm.card_support_eq_two.2 hs,
    Equiv.Perm.card_support_eq_two.2 ht, Equiv.Perm.card_support_eq_two.2 hu,
    Fintype.card_fin] at h
  omega

theorem exists_pair_of_isSwap {T : Set (Equiv.Perm (Fin 5))} (hT : ∀ t ∈ T, t.IsSwap)
    (hTc : T.Pairwise Commute) :
    ∃ s t : Equiv.Perm (Fin 5), T ⊆ {s, t} ∧ s * s = 1 ∧ t * t = 1 ∧ Commute s t := by
  have hsq : ∀ σ : Equiv.Perm (Fin 5), σ.IsSwap → σ * σ = 1 := by
    rintro σ ⟨a, b, -, rfl⟩
    exact Equiv.swap_mul_self a b
  by_cases h2 : ∃ s ∈ T, ∃ t ∈ T, s ≠ t
  · obtain ⟨s, hs, t, ht, hst⟩ := h2
    refine ⟨s, t, fun u hu => ?_, hsq s (hT s hs), hsq t (hT t ht), hTc hs ht hst⟩
    by_contra hu'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu'
    exact not_three_commuting_isSwap (hT s hs) (hT t ht) (hT u hu) hst (Ne.symm hu'.1)
      (Ne.symm hu'.2) (hTc hs ht hst) (hTc hs hu (Ne.symm hu'.1)) (hTc ht hu (Ne.symm hu'.2))
  · by_cases h1 : ∃ s, s ∈ T
    · obtain ⟨s, hs⟩ := h1
      refine ⟨s, s, fun u hu => Or.inl ?_, hsq s (hT s hs), hsq s (hT s hs), Commute.refl s⟩
      by_contra hus
      exact h2 ⟨u, hu, s, hs, hus⟩
    · exact ⟨1, 1, fun u hu => absurd ⟨u, hu⟩ h1, mul_one 1, mul_one 1, Commute.refl 1⟩

theorem card_closure_le_four {Γ : Type*} [Group Γ] {T : Set Γ} {s t : Γ} (hT : T ⊆ {s, t})
    (hs : s * s = 1) (ht : t * t = 1) (hst : Commute s t) :
    Nat.card (Subgroup.closure T) ≤ 4 := by
  classical
  have hs' : ∀ z, s * (s * z) = z := fun z => by rw [← mul_assoc, hs, one_mul]
  have hts : t * s = s * t := hst.eq.symm
  have hts' : ∀ z, t * (s * z) = s * (t * z) := fun z => by rw [← mul_assoc, hts, mul_assoc]
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hmem : ∀ x ∈ Subgroup.closure T, x = 1 ∨ x = s ∨ x = t ∨ x = s * t := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases (by simpa using hT hx : x = s ∨ x = t) with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp [mul_assoc, hs, ht, hs', hts, hts']
    | inv x _ hx =>
      rcases hx with rfl | rfl | rfl | rfl <;> simp [mul_inv_rev, hsi, hti, hts]
  let F : Finset Γ := {1, s, t, s * t}
  have hF : ∀ x ∈ Subgroup.closure T, x ∈ F := fun x hx => by
    simpa [F] using hmem x hx
  calc Nat.card (Subgroup.closure T) ≤ Nat.card F :=
        Nat.card_le_card_of_injective (fun x => ⟨x.1, hF x.1 x.2⟩)
          (fun a b h => Subtype.ext (Subtype.mk.inj h))
    _ = F.card := Nat.card_eq_finsetCard F
    _ ≤ 4 := Finset.card_le_four

theorem card_closure_le_four_of_isSwap {T : Set (Equiv.Perm (Fin 5))} (hT : ∀ t ∈ T, t.IsSwap)
    (hTc : T.Pairwise Commute) : Nat.card (Subgroup.closure T) ≤ 4 := by
  obtain ⟨s, t, hsub, hs, ht, hst⟩ := exists_pair_of_isSwap hT hTc
  exact card_closure_le_four hsub hs ht hst

end Swap

@[expose] def A38B42Concl {V : Type} [CommGroup V] [Finite V] (G L A : Subgroup (MulAut V)) :
    Prop :=
  (B42Case1 G L A ∧ ∃ n, 2 ≤ n ∧ BinaryNaturalSL L ⊤ ⊥ 2 n ∧ Nat.card V = 2 ^ (2 * n) ∧
      Nat.card ↥A = 2 ^ n) ∨
  (B42Case2 G L ∧ BinaryNaturalSL L ⊤ ⊥ 3 1 ∧ IsPSL 3 2 1 ↥L ∧ Nat.card V = 2 ^ 3) ∨
  (B42Case5 G A ∧ AlternatingNatural L ⊤ ⊥ 5 ∧ Nat.card V = 2 ^ 4 ∧ Nat.card ↥A ≤ 4)

@[expose] def A38B42 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L A : Subgroup (MulAut V), B4Hyp G L → A38Types ↥L → IsSimpleGroup ↥L →
      IsFFStarOffender G A → B42Conclusion G L A → A38B42Concl G L A

section Shape

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}

theorem a38B42Concl_of_isShapeGroup (hF : Facts10_1)
    (hV : ∀ v : V, v ^ 2 = 1) (hB : B4Hyp G L) (hA : IsFFStarOffender G A)
    (hc : B42Conclusion G L A) [hs : IsSimpleGroup ↥L] (hsh : IsShapeGroup ↥L) :
    A38B42Concl G L A := by
  have hcard := shapeCard_of_isShapeGroup hsh
  have hnc := InternalSec.exists_noncomm_of_isQuasisimple hB.2.2.1
  have hGL : G ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hB.2.1 ▸ le_normalizer_quasithinGenFitting G
  have hnt : Nontrivial ↥L := hs.toNontrivial
  have card_false : ∀ {N : ℕ}, Nat.card ↥L = N → ¬ ShapeCard N → False :=
    fun hN hnot => hnot (hN ▸ hcard)
  have one_le : ∀ {K : Type} [Field K] [Finite K] {n : ℕ}, Nat.card K = 2 ^ n → 1 ≤ n := by
    intro K _ _ n hK
    by_contra h
    have h0 : n = 0 := by omega
    have := Finite.one_lt_card (α := K)
    rw [hK, h0] at this
    norm_num at this
  rcases hc with h1 | h2 | ⟨⟨n, hsp, hJ⟩, -⟩ | ⟨⟨n, hg2, -, hJ⟩, -⟩ | h5 | ⟨-, ⟨π, hR⟩, -⟩ |
      ⟨-, -, ⟨α, π, hR⟩, -⟩ | ⟨-, -, -, K, _, _, Γ₀, -, -, hhat, -, π, hR, -⟩ |
      ⟨-, n, hn, hnat, -⟩ | ⟨⟨π, hR⟩, -⟩ | ⟨-, -, -, -, π, hR, -⟩
  ·
    obtain ⟨-, ⟨n, hnat⟩, ⟨hAL, hp, hodd⟩, -⟩ := id h1
    obtain ⟨K, _, _, hK, π, hπ⟩ := id hnat
    have e : ↥(StatedSL 2 K) ≃* ↥L :=
      MulEquiv.ofBijective π ⟨hπ.injective_of_faithful (FFModel.nat_faithful _), hπ.1⟩
    have h1n := one_le hK
    have hLc : Nat.card ↥L = 2 ^ n * (4 ^ n - 1) := by
      rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_two_pow hK]
    have h2n : 2 ≤ n := by
      by_contra hlt
      have hn1 : n = 1 := by omega
      subst hn1
      exact card_false (by rw [hLc]; norm_num) not_shapeCard_six
    refine Or.inl ⟨h1, n, h2n, hnat, ?_, ?_⟩
    · rw [card_eq_of_realizesVia_nat hπ, hK, Fintype.card_fin, ← pow_mul, mul_comm n 2]
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk⟩ := hp.exists_card_eq
      have hidx := Subgroup.card_mul_index (A.subgroupOf L)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hk, hLc] at hidx
      have h4 : 2 ∣ 4 ^ n := dvd_pow (by norm_num) (by omega)
      have hpos : 0 < 4 ^ n := by positivity
      have hodd' : ¬ 2 ∣ 4 ^ n - 1 := by omega
      rw [hk, eq_of_two_pow_mul_eq_of_not_dvd hodd hodd' hidx]
  ·
    obtain ⟨-, ⟨n, hnat⟩, -⟩ := id h2
    obtain ⟨K, _, _, hK, π, hπ⟩ := id hnat
    have e : ↥(StatedSL 3 K) ≃* ↥L :=
      MulEquiv.ofBijective π ⟨hπ.injective_of_faithful (FFModel.nat_faithful _), hπ.1⟩
    have h1n := one_le hK
    have hn1 : n = 1 := by
      by_contra hne
      refine card_false ?_ (not_shapeCard_SL_three (n := n) (by omega))
      rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_three_pow hK]
    subst hn1
    refine Or.inr (Or.inl ⟨h2, hnat, isPSL_three_two_of_mulEquiv hK e.symm, ?_⟩)
    rw [card_eq_of_realizesVia_nat hπ, hK, Fintype.card_fin]
    norm_num
  ·
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hsp.exists_equiv
    have h1 := one_le hFc
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hn1 : n = 1 := by omega
      subst hn1
      have hLJ := le_ffJ_of_two_dvd hV hB (two_dvd_card_ffJ hA)
      obtain ⟨N, hN, ⟨eN⟩⟩ := exists_normal_of_equiv e hLJ ((B6.ffJ_le G).trans hGL)
      have hq : CFSG.IsQuasisimple ↥N :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv eN.symm hB.2.2.1
      have h360 := hF.sp4Two F (by rw [hFc]; norm_num) N hN hq
      exact (card_false (by rw [← Nat.card_congr eN.toEquiv, h360]) not_shapeCard_360).elim
    · have hJL := hJ (by omega)
      rw [hJL] at e
      refine (card_false ?_ (not_shapeCard_Sp4 h1)).elim
      rw [← Nat.card_congr e.toEquiv, card_Sp4_pow hFc]
  ·
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain ⟨K, _, _, hKc, π, hR⟩ := hg2
      have h1 := one_le hKc
      have hn1 : n = 1 := by omega
      subst hn1
      have hLJ := le_ffJ_of_two_dvd hV hB (two_dvd_card_ffJ hA)
      have hLn : (L.subgroupOf (ffJ G)).Normal := by
        refine ⟨fun l hl h => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hl ⊢
        exact (Subgroup.mem_normalizer_iff.mp (((B6.ffJ_le G).trans hGL) h.2) l).mp hl
      have eL := Subgroup.subgroupOfEquivOfLe hLJ
      have hq : CFSG.IsQuasisimple ↥(L.subgroupOf (ffJ G)) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv eL.symm hB.2.2.1
      have h6048 := hF.g2Two K (by rw [hKc]; norm_num) _ π hR.1 _ hLn hq
      exact (card_false (by rw [← Nat.card_congr eL.toEquiv, h6048]) not_shapeCard_6048).elim
    · rw [hJ (by omega)] at hg2
      obtain ⟨K, _, _, hKc, π, hR⟩ := hg2
      exact absurd hR.1 (hF.g2 K n h2 hKc _ hsh π)
  ·
    obtain ⟨m, hm, halt, ⟨e⟩⟩ := InternalSec.alternatingNatural_of_b42Case5 hV hB h5
    rcases hm with rfl | rfl
    · have hV4 : Nat.card V = 2 ^ 4 := by
        obtain ⟨π, hπ⟩ := halt
        rw [card_eq_of_realizesVia_top hπ]
        exact card_altDn_mod_of_odd (n := 5) (by norm_num) (by decide)
      refine Or.inr (Or.inr ⟨h5, halt, hV4, ?_⟩)
      obtain ⟨⟨n, hn, π, hR, T, hT, hTc, hAT⟩, -⟩ := id h5
      have hn5 : n = 5 := by
        rcases hn with rfl | rfl
        · rfl
        · have h7 := card_eq_of_realizesVia_top hR
          rw [hV4] at h7
          have h7' := card_symDn_mod_of_odd (n := 7) (by norm_num) (by decide)
          change Nat.card (FFModel.symDn 7).Mod = _ at h7'
          rw [← h7] at h7'
          norm_num at h7'
      subst hn5
      have hinj := hR.injective_of_faithful (InternalSec.symDn_faithful le_rfl)
      calc Nat.card ↥A = Nat.card ↥(A.subgroupOf (ffJ G)) :=
            (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (B19.le_ffJ hA)).toEquiv).symm
        _ = Nat.card ↥(Subgroup.closure T) := by
            rw [hAT]
            exact Subgroup.card_map_of_injective hinj
        _ ≤ 4 := card_closure_le_four_of_isSwap hT hTc
    · refine (card_false ?_ not_shapeCard_2520).elim
      rw [Nat.card_congr e.toEquiv, card_alt 7 (by norm_num)]
      decide
  ·
    obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective (isSimpleGroup_alt (n := 6) (by norm_num)) π
      hR.1
    refine (card_false ?_ not_shapeCard_360).elim
    rw [← Nat.card_congr e.toEquiv, card_alt 6 (by norm_num)]
    decide
  ·
    obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective (isSimpleGroup_alt (n := 7) (by norm_num)) π
      hR.1
    refine (card_false ?_ not_shapeCard_2520).elim
    rw [← Nat.card_congr e.toEquiv, card_alt 7 (by norm_num)]
    decide
  ·
    have e : ↥Γ₀ ≃* ↥L := MulEquiv.ofBijective π
      ⟨hR.injective_of_faithful (FFModel.nat_faithful _), hR.1⟩
    have hc1 : Nat.card (Subgroup.center ↥L) = 1 := by
      rw [center_eq_bot_of_simple hnc, Subgroup.card_bot]
    have hc3 := hhat.2.1
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hc1] at hc3
    norm_num at hc3
  ·
    obtain ⟨F, _, _, hFc, ⟨e⟩⟩ := hnat.exists_equiv
    have hF2 : Nat.card F = 2 := by rw [hFc]; norm_num
    rcases hn with rfl | rfl
    · refine (card_false ?_ not_shapeCard_20160).elim
      rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_four_of_two hF2]
    · refine (card_false ?_ not_shapeCard_9999360).elim
      rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_five_of_two hF2]
  ·
    obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective
      (isSimpleGroup_statedSL_two (n := 4) (by norm_num)) π hR.1
    refine (card_false ?_ not_shapeCard_20160).elim
    rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_four_two]
  ·
    obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective
      (isSimpleGroup_statedSL_two (n := 5) (by norm_num)) π hR.1
    refine (card_false ?_ not_shapeCard_9999360).elim
    rw [← Nat.card_congr e.toEquiv, card_statedSL, card_SL_five_two]

end Shape

theorem a38B42_of (hF : Vol2.Ch10.SecA.Facts10_1) (hNS : Insp5aNonShape) :
    A38B42 := by
  intro V _ _ hV G L A hB hA38 hs hA hc
  by_cases hsh : IsShapeGroup ↥L
  · exact a38B42Concl_of_isShapeGroup hF hV hB hA hc hsh
  · exact ((hNS V G L hB hA38 hsh).1 A hA hc).elim

end CFSG.Quasithin.SmithD321
