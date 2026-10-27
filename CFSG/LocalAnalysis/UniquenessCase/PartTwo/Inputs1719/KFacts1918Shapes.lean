module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenTwenty
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1918AltSwap
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1918ThreeA6
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFacts1918OmegaPlusSix
import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ExtensionPCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

@[expose] def OmegaCentralizerShape : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (ε : Bool) (m : ℕ) (Y : Subgroup X),
    IsOmegaEps2 X ε m → IsCentralizerOfTransvectionIn X m Y →
      (m = 3 → ε = false → Nonempty (↥Y ≃* Equiv.Perm (Fin 6))) ∧ (m = 4 → IsSimpleGroup ↥Y)

variable {X : Type} [Group X] [Finite X]

private theorem closure_conj_mem_aux {G : Type} [Group G] {s : Set G} {c : G}
    (hc : ∀ x ∈ s, c * x * c⁻¹ ∈ s) {x : G}
    (hx : x ∈ Subgroup.closure s) : c * x * c⁻¹ ∈ Subgroup.closure s := by
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact Subgroup.subset_closure (hc y hy)
  | one => simp
  | mul a b _ _ iha ihb =>
    rw [show c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) by group]
    exact mul_mem iha ihb
  | inv a _ iha =>
    rw [show c * a⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ by group]
    exact inv_mem iha

private theorem oUpperTwo_subgroupOf_normal_self {G : Type} [Group G] [Finite G]
    (H : Subgroup G) : ((S17.oUpperTwo H).subgroupOf H).Normal := by
  rw [S17.oUpperTwo_eq_closure]
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  refine closure_conj_mem_aux ?_ hn
  rintro x ⟨hxH, hxodd⟩
  have hconj : orderOf ((g : G) * x * (g : G)⁻¹) = orderOf x := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  exact ⟨mul_mem (mul_mem g.2 hxH) (inv_mem g.2), by rw [hconj]; exact hxodd⟩

private theorem opp_subgroupOf_normal_self {G : Type} [Group G] [Finite G]
    (H : Subgroup G) : ((Opp 2 H).subgroupOf H).Normal := by
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  refine closure_conj_mem_aux ?_ hn
  rintro x ⟨hxH, k, hk⟩
  have hconj : orderOf ((g : G) * x * (g : G)⁻¹) = orderOf x := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  exact ⟨mul_mem (mul_mem g.2 hxH) (inv_mem g.2), k, by rw [hconj, hk]⟩

theorem kFacts1918_of_mulEquiv_perm (Y : Subgroup X) {k : ℕ} (hk : k = 3 ∨ 5 ≤ k)
    (e : ↥Y ≃* Equiv.Perm (Fin k)) :
    (∀ Nn : Subgroup X, Nn ≤ Opp 2 Y → (Nn.subgroupOf (Opp 2 Y)).Normal →
      ¬ Nn ≤ pCoreOf 2 (Opp 2 Y) → S17.oUpperTwo (Opp 2 Y) ≤ Nn ⊔ pCoreOf 2 (Opp 2 Y)) ∧
    Nat.card (Bar2 (S17.oUpperTwo (Opp 2 Y))) = k.factorial / 2 := by
  have hperm : CFSG.pCore 2 (Equiv.Perm (Fin k)) = ⊥ := by
    rcases hk with rfl | hk
    · exact CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.pCore_perm_eq_bot
        (Or.inr (Or.inl rfl))
    · exact CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.pCore_perm_eq_bot
        (Or.inr (Or.inr hk))
  have hp : CFSG.pCore 2 ↥Y = ⊥ := by
    have hmap := CFSG.pCore_map_iso 2 e
    rw [hperm] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap
  exact kFacts1918_of_perm Y hk e.toMonoidHom e.surjective
    ((MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective |>.trans hp.symm)

theorem kFacts1918_of_isSimpleGroup (Y : Subgroup X) (hY : IsSimpleGroup ↥Y)
    (h2 : 2 ∣ Nat.card Y) (hY2 : ¬ IsPGroup 2 ↥Y) :
    (∀ Nn : Subgroup X, Nn ≤ Opp 2 Y → (Nn.subgroupOf (Opp 2 Y)).Normal →
      ¬ Nn ≤ pCoreOf 2 (Opp 2 Y) → S17.oUpperTwo (Opp 2 Y) ≤ Nn ⊔ pCoreOf 2 (Opp 2 Y)) ∧
    Nat.card (Bar2 (S17.oUpperTwo (Opp 2 Y))) = Nat.card Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nonempty ↥Y := ⟨1⟩
  have hOpp : Opp 2 Y = Y := by
    refine le_antisymm ?_ ?_
    · unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
      exact (closure_le _).mpr fun x hx => hx.1
    · obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 2 h2
      have hz1 : z ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hz
        omega
      have hzOpp : (z : X) ∈ Opp 2 Y := by
        unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
        refine Subgroup.subset_closure ⟨z.2, 1, ?_⟩
        rw [Subgroup.orderOf_coe, hz, pow_one]
      have hN := opp_subgroupOf_normal_self Y
      haveI : ((Opp 2 Y).subgroupOf Y).Normal := hN
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Opp 2 Y).subgroupOf Y) with h | h
      · exfalso
        have hmem : z ∈ (Opp 2 Y).subgroupOf Y :=
          Subgroup.mem_subgroupOf.mpr hzOpp
        rw [h, Subgroup.mem_bot] at hmem
        exact hz1 hmem
      · exact Subgroup.subgroupOf_eq_top.mp h
  have hp : CFSG.pCore 2 ↥Y = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 ↥Y) with h | h
    · exact h
    · exfalso
      apply hY2
      have hp2 : IsPGroup 2 (CFSG.pCore 2 ↥Y) := CFSG.pCore_isPGroup
      rw [h] at hp2
      exact hp2.of_equiv Subgroup.topEquiv
  have ho : S17.oUpperTwo Y = Y := by
    refine le_antisymm (S17.oUpperTwo_le Y) ?_
    have hOddPrime : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card Y := by
      by_contra hcon
      apply hY2
      rw [IsPGroup.iff_card]
      refine ⟨(Nat.card Y).primeFactorsList.length, ?_⟩
      exact Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := ↥Y)).ne'
        (fun {d} hd hdn => by
          by_contra hd2
          exact hcon ⟨d, hd, hd2, hdn⟩)
    obtain ⟨p, hpp, hp2, hpdvd⟩ := hOddPrime
    haveI : Fact p.Prime := ⟨hpp⟩
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) p hpdvd
    have hpodd : Odd p := hpp.odd_of_ne_two hp2
    have hw1 : w ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hw
      exact hpp.ne_one hw.symm
    have hwodd : Odd (orderOf (w : X)) := by
      rw [Subgroup.orderOf_coe, hw]
      exact hpodd
    have hwmem : (w : X) ∈ S17.oUpperTwo Y := by
      rw [S17.oUpperTwo_eq_closure]
      exact Subgroup.subset_closure ⟨w.2, hwodd⟩
    have hN := oUpperTwo_subgroupOf_normal_self Y
    haveI : ((S17.oUpperTwo Y).subgroupOf Y).Normal := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((S17.oUpperTwo Y).subgroupOf Y) with h | h
    · exfalso
      have hmem : w ∈ (S17.oUpperTwo Y).subgroupOf Y :=
        Subgroup.mem_subgroupOf.mpr hwmem
      rw [h, Subgroup.mem_bot] at hmem
      exact hw1 hmem
    · exact Subgroup.subgroupOf_eq_top.mp h
  have hpco : pCoreOf 2 (Opp 2 Y) = ⊥ := by
    rw [hOpp]
    simp only [pCoreOf, hp, Subgroup.map_bot]
  constructor
  · intro Nn hNnOpp hNnNorm hNnNot
    have hNnY : Nn ≤ Y := hOpp ▸ hNnOpp
    have hNnNormY : (Nn.subgroupOf Y).Normal := by rwa [hOpp] at hNnNorm
    haveI : (Nn.subgroupOf Y).Normal := hNnNormY
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Nn.subgroupOf Y) with h | h
    · exfalso
      apply hNnNot
      rw [hpco, le_bot_iff]
      exact (Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le hNnY
    · have hYNn : Y ≤ Nn := Subgroup.subgroupOf_eq_top.mp h
      rw [hOpp, ho]
      exact le_sup_of_le_left hYNn
  · rw [hOpp, ho]
    change Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = Nat.card Y
    rw [hp]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := ↥Y)).toEquiv

private theorem kFacts1918_of_quot_perm {k : ℕ} (hk : k = 3 ∨ 5 ≤ k) (Y : Subgroup X)
    (e : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* Equiv.Perm (Fin k)) :
    (∀ Nn : Subgroup X, Nn ≤ Opp 2 Y → (Nn.subgroupOf (Opp 2 Y)).Normal →
      ¬ Nn ≤ pCoreOf 2 (Opp 2 Y) → S17.oUpperTwo (Opp 2 Y) ≤ Nn ⊔ pCoreOf 2 (Opp 2 Y)) ∧
    Nat.card (Bar2 (S17.oUpperTwo (Opp 2 Y))) = k.factorial / 2 := by
  have hsurj : Function.Surjective
      (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))).ker =
      CFSG.pCore 2 ↥Y :=
    (MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective).trans
      (QuotientGroup.ker_mk' _)
  exact kFacts1918_of_perm Y hk _ hsurj hker

theorem kFacts1918_of_shape (hΩ : OmegaCentralizerShape) (Y : Subgroup X)
    (h : Shape19_16_124 X Y) :
    (∀ Nn : Subgroup X, Nn ≤ Opp 2 Y → (Nn.subgroupOf (Opp 2 Y)).Normal →
      ¬ Nn ≤ pCoreOf 2 (Opp 2 Y) → S17.oUpperTwo (Opp 2 Y) ≤ Nn ⊔ pCoreOf 2 (Opp 2 Y)) ∧
    Nat.card (Bar2 (S17.oUpperTwo (Opp 2 Y))) ∈ ({3, 60, 360, 20160, 1451520} : Finset ℕ) := by
  rcases h with ⟨_, hcase⟩ | ⟨hA6, hidx⟩ | ⟨m, hm, hcase⟩
  · rcases hcase with h3 | h5 | h6
    · obtain ⟨e⟩ := h3
      have hk := kFacts1918_of_quot_perm (k := 3) (Or.inl rfl) Y e
      exact ⟨hk.1, by rw [hk.2]; norm_num [Nat.factorial]⟩
    · obtain ⟨e⟩ := h5
      have hk := kFacts1918_of_quot_perm (k := 5) (Or.inr (by norm_num)) Y e
      exact ⟨hk.1, by rw [hk.2]; norm_num [Nat.factorial]⟩
    · obtain ⟨e⟩ := h6
      have hk := kFacts1918_of_quot_perm (k := 6) (Or.inr (by norm_num)) Y e
      exact ⟨hk.1, by rw [hk.2]; norm_num [Nat.factorial]⟩
  · have hk := kFacts1918_of_isA6ModZ3 hA6 Y hidx
    exact ⟨hk.1, by rw [hk.2]; norm_num⟩
  · rcases hcase with ⟨ε, hΩX, hCent⟩ | ⟨hAlt, e, a, b, hab, hmap⟩
    · rcases hm with rfl | rfl
      · cases ε with
        | true =>
          obtain ⟨e, a, b, hab, hmap⟩ :=
            exists_swap_of_isOmegaPlus_six (by simpa [IsOmegaEps2] using hΩX) hCent
          have hk := kFacts1918_of_alt_swap (Y := Y) (n := 2 * 3 + 2) (by norm_num) e hab hmap
          exact ⟨hk.1, by rw [hk.2]; norm_num [Nat.factorial]⟩
        | false =>
          obtain ⟨e⟩ := (hΩ X false 3 Y hΩX hCent).1 rfl rfl
          have hk := kFacts1918_of_mulEquiv_perm Y (k := 6) (Or.inr (by norm_num)) e
          exact ⟨hk.1, by rw [hk.2]; norm_num [Nat.factorial]⟩
      · have hSimple : IsSimpleGroup ↥Y := (hΩ X ε 4 Y hΩX hCent).2 rfl
        obtain ⟨τ, hτ2, hτout, hYfix, hYcard⟩ := hCent
        have hYc : Nat.card Y = 1451520 := by
          rw [if_neg (by norm_num : ¬ (4 = 3))] at hYcard
          exact hYcard
        have h2 : 2 ∣ Nat.card Y := by rw [hYc]; norm_num
        have hY2 : ¬ IsPGroup 2 ↥Y := by
          intro hp
          obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
          have h3 : 3 ∣ Nat.card Y := by rw [hYc]; norm_num
          rw [hn] at h3
          exact (by norm_num : ¬ (3 : ℕ) ∣ 2)
            (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
        have hk := kFacts1918_of_isSimpleGroup Y hSimple h2 hY2
        exact ⟨hk.1, by rw [hk.2, hYc]; norm_num⟩
    · rcases hm with rfl | rfl
      · have hk := kFacts1918_of_alt_swap (Y := Y) (n := 2 * 3 + 2) (by norm_num) e hab hmap
        exact ⟨hk.1, by rw [hk.2]; norm_num [Nat.factorial]⟩
      · have hk := kFacts1918_of_alt_swap (Y := Y) (n := 2 * 4 + 2) (by norm_num) e hab hmap
        exact ⟨hk.1, by rw [hk.2]; norm_num [Nat.factorial]⟩

theorem k_19_18_minNormal_of_omegaCentralizerShape (hΩ : OmegaCentralizerShape) :
    K_19_18_minNormal :=
  fun _ _ _ Y h => (kFacts1918_of_shape hΩ Y h).1

theorem k_19_20_J0shape_of_omegaCentralizerShape (hΩ : OmegaCentralizerShape) :
    K_19_20_J0shape :=
  fun _ _ _ Y h => (kFacts1918_of_shape hΩ Y h).2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
