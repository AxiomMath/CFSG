module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVNine
import CFSG.RankThree.PartTwo.KFacts.KS21AutThreeU58
import CFSG.RankThree.PartTwo.Sec21.Item229Orders
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven (projSU)
open Item434Kit Item434Alt
open scoped Pointwise

namespace Item434SmallTwoIV

theorem factorization_card_projSU_five_eight :
    (Nat.card (projSU 5 2 3)).factorization 3 = 9 := by
  rw [Sec21.card_projSU (m := 5) (by norm_num) (by norm_num),
    show CFSG.Open.ordTwistedA (5 - 1) (2 ^ 3) = 3 ^ 9 * 236583028271349760 by decide]
  exact Item434AltPerm.factorization_three_pow_mul 9 (by norm_num)

theorem exists_sylow_fixed {X : Type*} [Group X] [Finite X] {S : Subgroup (MulAut X)}
    (hS : IsPGroup 3 S) :
    ∃ P : Sylow 3 X, ∀ α ∈ S, (P : Subgroup X).map α.toMonoidHom = P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnd : ¬ 3 ∣ Nat.card (Sylow 3 X) := by
    have h := card_sylow_modEq_one 3 X
    rintro ⟨k, hk⟩
    unfold Nat.ModEq at h
    rw [hk] at h
    omega
  obtain ⟨P, hP⟩ := hS.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 3 X) hnd
  refine ⟨P, fun α hα => ?_⟩
  have h2 : α • P = P := hP ⟨α, hα⟩
  have h3 := congrArg (fun Q : Sylow 3 X => (Q : Subgroup X)) h2
  simp only [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at h3
  exact h3

theorem relIndex_fixingSubgroup_le {X : Type*} [Group X] [Finite X] {S : Subgroup (MulAut X)}
    {P N T : Subgroup X} (hTN : T ≤ N) (hNc : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hdec : ∀ α ∈ S, ∃ p ∈ P, ∀ t ∈ T, α t = p * t * p⁻¹) :
    (fixingSubgroup (MulAut X) (T : Set X)).relIndex S ≤ N.relIndex P := by
  choose! pα hpα hpαt using hdec
  set F := fixingSubgroup (MulAut X) (T : Set X) with hF
  let Φ : (S ⧸ F.subgroupOf S) → (P ⧸ N.subgroupOf P) :=
    fun q => (⟨pα ((Quotient.out q : S) : MulAut X), hpα _ (Quotient.out q : S).2⟩ : P)
  have hΦ : Function.Injective Φ := by
    intro q₁ q₂ hq
    have hn := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hq)
    set α₁ : S := Quotient.out q₁ with hα₁
    set α₂ : S := Quotient.out q₂ with hα₂
    have hn' : (pα (α₁ : MulAut X))⁻¹ * pα (α₂ : MulAut X) ∈ N := hn
    have hagree : ∀ t ∈ T, (α₂ : MulAut X) t = (α₁ : MulAut X) t := by
      intro t ht
      rw [hpαt _ α₂.2 t ht, hpαt _ α₁.2 t ht]
      set p₁ := pα (α₁ : MulAut X)
      set p₂ := pα (α₂ : MulAut X)
      have hc := hNc _ hn' t (hTN ht)
      have hp₂ : p₂ = p₁ * (p₁⁻¹ * p₂) := by group
      rw [hp₂]
      calc p₁ * (p₁⁻¹ * p₂) * t * (p₁ * (p₁⁻¹ * p₂))⁻¹ =
          p₁ * ((p₁⁻¹ * p₂) * t) * (p₁⁻¹ * p₂)⁻¹ * p₁⁻¹ := by group
        _ = p₁ * (t * (p₁⁻¹ * p₂)) * (p₁⁻¹ * p₂)⁻¹ * p₁⁻¹ := by rw [hc]
        _ = p₁ * t * p₁⁻¹ := by group
    rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂, QuotientGroup.eq,
      Subgroup.mem_subgroupOf, ← hα₁, ← hα₂, hF, mem_fixingSubgroup_iff]
    intro t ht
    change ((α₁ : MulAut X)⁻¹ * (α₂ : MulAut X)) t = t
    rw [MulAut.mul_apply, hagree t ht, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  change Nat.card (S ⧸ F.subgroupOf S) ≤ Nat.card (P ⧸ N.subgroupOf P)
  exact Nat.card_le_card_of_injective Φ hΦ

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem false_of_u58_27 (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSU 5 2 3)
    (h27 : Nat.card (A.map (layerConj G)) = 27) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (projSU 5 2 3) := Finite.of_equiv _ e₀.toEquiv
  have h27' : Nat.card h.layerStar = 27 := h27
  have hZ : Subgroup.center (layer G) = ⊥ := by
    rcases h.card_layerStar with h9 | ⟨-, hZ⟩
    · omega
    · exact hZ
  set Astar := A.map (quotConj e₀) with hAstar
  have hAe : CFSG.Assembly.IsElemAbelian 3 Astar := isElemAbelian_map_quotConj h e₀
  have hA27 : Nat.card Astar = 27 := by rw [Item434Spor.card_map_quotConj h e₀, h27']
  obtain ⟨P, hP⟩ := exists_sylow_fixed (Sec5.isPGroup_of_isElemAbelian hAe)
  have hPcard : Nat.card (P : Subgroup (projSU 5 2 3)) = 3 ^ 9 := by
    rw [Sylow.card_eq_multiplicity, factorization_card_projSU_five_eight]
  obtain ⟨N, E, hN, hNcard, hEN, hE, hE81⟩ := exists_torus_projSU_five_eight
  have hN3 : IsPGroup 3 N := IsPGroup.of_card (n := 8) hNcard
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card (P₀ := (P : Subgroup _))
    (Sylow.card_eq_multiplicity P) hN3
  set N' := N.map (MulAut.conj g⁻¹).toMonoidHom with hN'
  set T₀ := E.map (MulAut.conj g⁻¹).toMonoidHom with hT₀
  have hN'P : N' ≤ P := Item434AltPerm.map_conj_inv_le hg
  have hT₀N' : T₀ ≤ N' := Subgroup.map_mono hEN
  have hN'card : Nat.card N' = 3 ^ 8 :=
    (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).trans hNcard
  have hT₀card : Nat.card T₀ = 81 :=
    (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).trans hE81
  have hT₀e : CFSG.Assembly.IsElemAbelian 3 T₀ :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ E hE
  have hN'c : ∀ x ∈ N', ∀ y ∈ N', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (hN.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  have hAT := KFacts.KS21.U58.autThree_projSU P T₀ (hT₀N'.trans hN'P) hT₀e
    (by rw [hT₀card]; norm_num)
  have hdec : ∀ α ∈ Astar, ∃ p ∈ (P : Subgroup (projSU 5 2 3)), ∀ t ∈ T₀,
      α t = p * t * p⁻¹ := by
    intro α hα
    obtain ⟨p, hp, φ, -, hφ, hαe⟩ := hAT α ⟨1, by rw [pow_one]; exact hAe.2 α hα⟩ (hP α hα)
    refine ⟨p, hp, fun t ht => ?_⟩
    rw [hαe, MulAut.mul_apply, hφ t ht, MulAut.conj_apply]
  set F := fixingSubgroup (MulAut (projSU 5 2 3)) (T₀ : Set (projSU 5 2 3)) with hF
  have hPN' : N'.relIndex P = 3 := by
    have h1 := Subgroup.relIndex_mul_card N' P
    rw [inf_eq_left.mpr hN'P, hN'card, hPcard] at h1
    have h3 : (3 : ℕ) ^ 9 = 3 * 3 ^ 8 := by norm_num
    rw [h3] at h1
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h1
  have hrel : F.relIndex Astar ≤ 3 := by
    have h1 := relIndex_fixingSubgroup_le (S := Astar) (P := (P : Subgroup (projSU 5 2 3)))
      hT₀N' hN'c hdec
    rw [hPN'] at h1
    exact h1
  have hK9 : 9 ≤ Nat.card (F ⊓ Astar : Subgroup (MulAut (projSU 5 2 3))) := by
    have h1 := Subgroup.relIndex_mul_card F Astar
    rw [hA27] at h1
    by_contra hlt
    push Not at hlt
    have h2 : F.relIndex Astar * Nat.card (F ⊓ Astar : Subgroup (MulAut (projSU 5 2 3))) ≤
        3 * 8 := Nat.mul_le_mul hrel (by omega)
    omega
  refine false_of_fixed h hZ e₀ (B := A ⊓ (F ⊓ Astar).comap (quotConj e₀)) inf_le_left
    (hK9.trans (card_le_card_inf_comap e₀ inf_le_right)) hT₀e hT₀card.ge ?_
  rintro b ⟨-, hb⟩ d hd
  have := (mem_fixingSubgroup_iff _).mp (Subgroup.mem_comap.mp hb).1 d hd
  rwa [MulAut.smul_def] at this

end Item434SmallTwoIV

open Item434SmallTwoIV

section Families


theorem item434SmallTwoIV_U58_27 : Item434SecForCard IsSmallTwoU58 27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  exact (false_of_u58_27 hc e₀ h27).elim

theorem item434SmallTwoIV_U58_of (hT : Census.TripleCoverLie) : Item434SmallTwoIV_U58 :=
  item434SecFor_of_card (item434SmallTwoIV_U58_9_of hT) item434SmallTwoIV_U58_27

end Families

end CFSG.RankThree.PartTwo.Sec4
