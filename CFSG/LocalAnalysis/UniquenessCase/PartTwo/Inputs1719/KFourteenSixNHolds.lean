module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSix
public import CFSG.HardMathSupport.Solomon.Coordinator.Generation228

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixN

open Subgroup

variable {G : Type} [Group G] [Finite G] {N T A K : Subgroup G} {r : ℕ}

theorem Hyp146N.commutator_pCoreOf_eq (h : Hyp146N N T A r) :
    ⁅CFSG.Open.pCoreOf 2 (A ⊔ T), A⁆ =
      ⁅CFSG.Open.pCoreOf 2 (A ⊔ T) ⊓ UC22.conjClosure N A, A⁆ := by
  let H := UC22.conjClosure N A
  let X := CFSG.Open.pCoreOf 2 (A ⊔ T)
  have hA : IsPGroup r A := IsPGroup.of_card (n := 1) (by rw [h.card, pow_one])
  have hX2 : IsPGroup 2 X := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (A ⊔ T)
  have hATN : A ⊔ T ≤ N := sup_le h.le h.sylow.le
  have hXN : X ≤ N := (CFSG.LieType.BorelTits.pCoreOf_le 2 (A ⊔ T)).trans hATN
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    (le_sup_left : A ≤ A ⊔ T).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (A ⊔ T))
  have hAH : A ≤ H := UC22.uc22p22v_le_conjClosure N A
  have hNH : N ≤ Subgroup.normalizer (H : Set G) :=
    UC22.uc22p22v_le_normalizer_conjClosure N A
  have hXH : ⁅X, A⁆ ≤ H := by
    rw [Subgroup.commutator_le]
    intro x hx a ha
    rw [commutatorElement_def]
    have hxN : x ∈ N := hXN hx
    have haH : a ∈ H := hAH ha
    have hconj : x * a * x⁻¹ ∈ H :=
      (Subgroup.le_normalizer_iff.mp hNH) x hxN a haH
    exact H.mul_mem hconj (H.inv_mem haH)
  have hXinf : ⁅X, A⁆ ≤ X ⊓ H :=
    le_inf (CFSG.HardMathSupport.Solomon.Coordinator.Generation228.comm_le_of_le_normalizer
      hAX) hXH
  have hnot : ¬ r ∣ Nat.card X := by
    obtain ⟨k, hk⟩ := hX2.exists_card_eq
    rw [hk]
    intro hdvd
    have hr2 : r ≠ 2 := by have := h.three_lt; omega
    exact hr2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1
      (h.prime.dvd_of_dvd_pow hdvd))
  have hfix : ⁅⁅X, A⁆, A⁆ = ⁅X, A⁆ :=
    CFSG.HardMathSupport.Solomon.Coordinator.Generation228.comm_comm_eq
      h.prime hA hAX hnot
  refine le_antisymm ?_ (Subgroup.commutator_mono inf_le_left le_rfl)
  calc ⁅X, A⁆ = ⁅⁅X, A⁆, A⁆ := hfix.symm
    _ ≤ ⁅X ⊓ H, A⁆ := Subgroup.commutator_mono hXinf le_rfl

theorem Hyp146N.commutator_le_of_isSolvable (h : Hyp146N N T A r)
    (hsol : Group.IsSolvable ↥(UC22.conjClosure N A)) :
    ⁅CFSG.Open.pCoreOf 2 (A ⊔ T), A⁆ ≤ CFSG.Open.pCoreOf 2 (UC22.conjClosure N A) := by
  let H := UC22.conjClosure N A
  let X := CFSG.Open.pCoreOf 2 (A ⊔ T)
  have hA : IsPGroup r A := IsPGroup.of_card (n := 1) (by rw [h.card, pow_one])
  have hX2 : IsPGroup 2 X := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (A ⊔ T)
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    (le_sup_left : A ≤ A ⊔ T).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (A ⊔ T))
  have hAHn : A ≤ Subgroup.normalizer (H : Set G) :=
    h.le.trans (UC22.uc22p22v_le_normalizer_conjClosure N A)
  have hS2 : IsPGroup 2 ↥(X ⊓ H) := hX2.to_le inf_le_left
  have hAS : A ≤ Subgroup.normalizer (X ⊓ H : Set G) :=
    (le_inf hAX hAHn).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hr4 : 4 < r := by
    have h3 : 3 < r := h.three_lt
    rcases lt_or_ge 4 r with h4 | h4
    · exact h4
    · have hr : r = 4 := by omega
      have hp : r.Prime := h.prime
      rw [hr] at hp
      norm_num at hp
  have hcomm : ⁅X ⊓ H, A⁆ ≤ CFSG.Open.pCoreOf 2 H :=
    commutator_le_pCoreOf_of_isSolvable (N := N) (Y := H) (S := X ⊓ H) (A := A)
      h.prime hr4 hA h.conjClosure_le hsol hAHn inf_le_right hS2 hAS
      h.rank_three h.rank_two
  rw [h.commutator_pCoreOf_eq]
  exact hcomm

theorem Hyp146N.commutator_inf_le_OInf (h : Hyp146N N T A r)
    (hC : ∀ Q : Subgroup (UC22.BarInf (UC22.conjClosure N A)), IsPGroup 2 Q →
      barIn (UC22.conjClosure N A) A ≤
        normalizer (Q : Set (UC22.BarInf (UC22.conjClosure N A))) →
      ⁅Q, barIn (UC22.conjClosure N A) A⁆ = ⊥) :
    ⁅CFSG.Open.pCoreOf 2 (A ⊔ T) ⊓ UC22.conjClosure N A, A⁆ ≤
      UC22.OInf (UC22.conjClosure N A) := by
  let H := UC22.conjClosure N A
  let X := CFSG.Open.pCoreOf 2 (A ⊔ T)
  let S := X ⊓ H
  let f := QuotientGroup.mk' (CFSG.solvableRadical ↥H)
  have hS2 : IsPGroup 2 S :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (A ⊔ T)).to_le inf_le_left
  have hSH : S ≤ H := inf_le_right
  have hAH : A ≤ H := UC22.uc22p22v_le_conjClosure N A
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    (le_sup_left : A ≤ A ⊔ T).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (A ⊔ T))
  have hAHn : A ≤ Subgroup.normalizer (H : Set G) :=
    h.le.trans (UC22.uc22p22v_le_normalizer_conjClosure N A)
  have hAS : A ≤ Subgroup.normalizer (S : Set G) :=
    (le_inf hAX hAHn).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hQS : IsPGroup 2 ↥(barIn H S) :=
    (hS2.comap_subtype (K := H)).map f
  have hnorm : barIn H A ≤
      Subgroup.normalizer (barIn H S : Set (UC22.BarInf H)) := by
    exact CFSG.GroupTheory.map_subgroupOf_le_normalizer (M := H) f hAS
  have hbar : ((⁅S, A⁆).subgroupOf H).map f = ⊥ := by
    rw [← CFSG.GroupTheory.commutator_subgroupOf_eq hSH hAH, Subgroup.map_commutator]
    change ⁅barIn H S, barIn H A⁆ = ⊥
    exact hC (barIn H S) hQS hnorm
  have hle : (⁅S, A⁆).subgroupOf H ≤ f.ker :=
    (Subgroup.map_eq_bot_iff (f := f) ((⁅S, A⁆).subgroupOf H)).mp hbar
  have hSA : ⁅S, A⁆ ≤ S :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hAS
  intro y hy
  have hyH : y ∈ H := hSH (hSA hy)
  have hmem : (⟨y, hyH⟩ : ↥H) ∈ f.ker :=
    hle (by simpa only [S, Subgroup.mem_subgroupOf] using hy)
  rw [QuotientGroup.ker_mk'] at hmem
  exact Subgroup.mem_map_of_mem H.subtype hmem

theorem Hyp146N.commutator_inf_le_pCoreOf_OInf (h : Hyp146N N T A r)
    (hC : ∀ Q : Subgroup (UC22.BarInf (UC22.conjClosure N A)), IsPGroup 2 Q →
      barIn (UC22.conjClosure N A) A ≤
        normalizer (Q : Set (UC22.BarInf (UC22.conjClosure N A))) →
      ⁅Q, barIn (UC22.conjClosure N A) A⁆ = ⊥) :
    ⁅CFSG.Open.pCoreOf 2 (A ⊔ T) ⊓ UC22.conjClosure N A, A⁆ ≤
      CFSG.Open.pCoreOf 2 (UC22.OInf (UC22.conjClosure N A)) := by
  let H := UC22.conjClosure N A
  let X := CFSG.Open.pCoreOf 2 (A ⊔ T)
  let S := X ⊓ H
  let R := UC22.OInf H
  have hA : IsPGroup r A := IsPGroup.of_card (n := 1) (by rw [h.card, pow_one])
  have hX2 : IsPGroup 2 X := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (A ⊔ T)
  have hS2 : IsPGroup 2 S := hX2.to_le inf_le_left
  have hSH : S ≤ H := inf_le_right
  have hAH : A ≤ H := UC22.uc22p22v_le_conjClosure N A
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    (le_sup_left : A ≤ A ⊔ T).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (A ⊔ T))
  have hAHn : A ≤ Subgroup.normalizer (H : Set G) :=
    h.le.trans (UC22.uc22p22v_le_normalizer_conjClosure N A)
  have hAS : A ≤ Subgroup.normalizer (S : Set G) :=
    (le_inf hAX hAHn).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hRH : R ≤ H := Subgroup.map_subtype_le (CFSG.solvableRadical ↥H)
  have hS'R : ⁅S, A⁆ ≤ R := h.commutator_inf_le_OInf hC
  have hS'2 : IsPGroup 2 ↥⁅S, A⁆ :=
    hS2.to_le ((Subgroup.le_normalizer_iff_commutator_le_left).mp hAS)
  have hAS' : A ≤ Subgroup.normalizer ((⁅S, A⁆ : Subgroup G) : Set G) := by
    rw [Subgroup.commutator_comm S A]
    exact Subgroup.normalizer_commutator_ge_left (H₁ := A) (H₂ := S)
  have hRsolv : Group.IsSolvable ↥R := by
    have hsolS : Group.IsSolvable ↥(CFSG.solvableRadical ↥H) :=
      CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
    exact @Group.isSolvable_of_surjective ↥(CFSG.solvableRadical ↥H)
      ↥((CFSG.solvableRadical ↥H).map H.subtype) _ _
      (MonoidHom.subgroupMap H.subtype (CFSG.solvableRadical ↥H))
      (MonoidHom.subgroupMap_surjective H.subtype (CFSG.solvableRadical ↥H)) hsolS
  have hHNR : H ≤ Subgroup.normalizer (R : Set G) := by
    have hN : (R.subgroupOf H).Normal := by
      rw [show R.subgroupOf H = CFSG.solvableRadical ↥H from
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective _]
      infer_instance
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hRH).mp hN
  have hRN : R ≤ N := hRH.trans h.conjClosure_le
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := hAH.trans hHNR
  have hr4 : 4 < r := by
    have h3 : 3 < r := h.three_lt
    rcases lt_or_ge 4 r with h4 | h4
    · exact h4
    · have hr : r = 4 := by omega
      have hp : r.Prime := h.prime
      rw [hr] at hp
      norm_num at hp
  have hstep : ⁅⁅S, A⁆, A⁆ ≤ CFSG.Open.pCoreOf 2 R :=
    commutator_le_pCoreOf_of_isSolvable (N := N) (Y := R) (S := ⁅S, A⁆) (A := A)
      h.prime hr4 hA hRN hRsolv hAR hS'R hS'2 hAS' h.rank_three h.rank_two
  have hnot : ¬ r ∣ Nat.card S := by
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    rw [hk]
    intro hdvd
    have hr2 : r ≠ 2 := by have := h.three_lt; omega
    exact hr2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1
      (h.prime.dvd_of_dvd_pow hdvd))
  have hfix : ⁅⁅S, A⁆, A⁆ = ⁅S, A⁆ :=
    CFSG.HardMathSupport.Solomon.Coordinator.Generation228.comm_comm_eq
      h.prime hA hAS hnot
  rw [hfix] at hstep
  exact hstep

theorem Hyp146N.pCoreOf_OInf_le_pCoreOf :
    CFSG.Open.pCoreOf 2 (UC22.OInf (UC22.conjClosure N A)) ≤
      CFSG.Open.pCoreOf 2 (UC22.conjClosure N A) := by
  let H := UC22.conjClosure N A
  let R := UC22.OInf H
  have hRH : R ≤ H := Subgroup.map_subtype_le (CFSG.solvableRadical ↥H)
  have hHNR : H ≤ Subgroup.normalizer (R : Set G) := by
    have hN : (R.subgroupOf H).Normal := by
      rw [show R.subgroupOf H = CFSG.solvableRadical ↥H from
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective _]
      infer_instance
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hRH).mp hN
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 R)
  · exact (CFSG.LieType.BorelTits.pCoreOf_le 2 R).trans hRH
  · exact hHNR.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 R)

theorem Hyp146N.commutator_le_of_barTwo (h : Hyp146N N T A r)
    (hC : ∀ Q : Subgroup (UC22.BarInf (UC22.conjClosure N A)), IsPGroup 2 Q →
      barIn (UC22.conjClosure N A) A ≤ normalizer (Q : Set (UC22.BarInf (UC22.conjClosure N A))) →
        ⁅Q, barIn (UC22.conjClosure N A) A⁆ = ⊥) :
    ⁅CFSG.Open.pCoreOf 2 (A ⊔ T), A⁆ ≤ CFSG.Open.pCoreOf 2 (UC22.conjClosure N A) := by
  rw [h.commutator_pCoreOf_eq]
  exact (h.commutator_inf_le_pCoreOf_OInf hC).trans Hyp146N.pCoreOf_OInf_le_pCoreOf

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixN

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open KFourteenSixN

theorem k_UC146N_of_bar (hbar : K_UC146N_Bar) : K_UC146N := by
  intro G _ _ N T A K r hK hT hr hr3 hn hAN hA hAT h3 hrr hs hATK hNK
  have h : Hyp146N N T A r := ⟨hK, hT, hr, hr3, hn, hAN, hA, hAT, h3, hrr, hs⟩
  by_cases hsol : Group.IsSolvable ↥(UC22.conjClosure N A)
  · exact Or.inr (Or.inl ⟨h.commutator_le_of_isSolvable hsol, Or.inl hsol⟩)
  · rcases h.bar_cases hbar hsol with h1 | h2 | h3'
    · exact Or.inl (h.conjClosure_le_of_barOne hsol hATK hNK h1)
    · exact Or.inr (Or.inl ⟨h.commutator_le_of_barTwo h2.2.2, Or.inr ⟨h2.1, h2.2.1⟩⟩)
    · exact Or.inr (Or.inr (h.exists_perfect_of_barThree hsol hATK hNK h3'))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
