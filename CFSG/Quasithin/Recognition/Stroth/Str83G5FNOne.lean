module

public import CFSG.Quasithin.Recognition.Stroth.BenderH7
import CFSG.Quasithin.Background.D14Chief
import CFSG.GroupTheory.ChiefFactors.OddElement
import CFSG.GroupTheory.CommutatorMemSubgroup

public section

namespace CFSG.Quasithin.Stroth.G5F

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}

private lemma le_normalizer_sup_of_commutator_mem {L N Q : Subgroup G}
    (hNQ : N ≤ Subgroup.normalizer (Q : Set G)) (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hLN : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ * n⁻¹ ∈ Q) :
    L ≤ Subgroup.normalizer ((N ⊔ Q : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro l hl k hk
  have hk' : k ∈ Q ⊔ N := by rw [sup_comm]; exact hk
  obtain ⟨q, hq, n, hn, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hNQ).mp hk'
  have hql : l * q * l⁻¹ ∈ Q := (Subgroup.le_normalizer_iff.mp hLQ) l hl q hq
  have hnl : l * n * l⁻¹ ∈ N ⊔ Q := by
    have hc : l * n * l⁻¹ * n⁻¹ ∈ Q := hLN l hl n hn
    have heq : l * n * l⁻¹ = (l * n * l⁻¹ * n⁻¹) * n := by group
    rw [heq]
    exact (N ⊔ Q).mul_mem (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hn)
  have hprod : l * (q * n) * l⁻¹ = (l * q * l⁻¹) * (l * n * l⁻¹) := by group
  rw [hprod]
  exact (N ⊔ Q).mul_mem (Subgroup.mem_sup_right hql) hnl

theorem n1_chief_dichotomy (hF : Hyp111 L1 L2 S) (hLS : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S)
    {N1 : Subgroup G} (hN1P : N1 ≤ P1 L1 L2 S)
    (hN1L : ∀ x ∈ N1, ∀ l ∈ L1, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L1)
    {L R : Subgroup G} (hstep : IsChiefStep (L1 ⊔ S ⊔ N1) (Q1 L1 L2 S) L R) :
    (∀ x ∈ N1, ∀ r ∈ R, x * r * x⁻¹ * r⁻¹ ∈ L) ∨
      ∀ r ∈ R, (∀ x ∈ N1, x * r * x⁻¹ * r⁻¹ ∈ L) → r ∈ L := by
  classical
  have hQ2 : IsPGroup 2 ↥(Q1 L1 L2 S) := pCoreOf_isPGroup 2 (P1 L1 L2 S)
  have hL1P : L1 ≤ P1 L1 L2 S := le_sup_left
  have hSP : S ≤ P1 L1 L2 S := (le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right
  have hXP : L1 ⊔ S ⊔ N1 ≤ P1 L1 L2 S := sup_le (sup_le hL1P hSP) hN1P
  have hN1X : N1 ≤ L1 ⊔ S ⊔ N1 := le_sup_right
  have hQX : Q1 L1 L2 S ≤ L1 ⊔ S ⊔ N1 := by
    have h : Q1 L1 L2 S ≤ L1 ⊔ S := by rw [hLS]; exact le_sup_right
    exact h.trans le_sup_left
  have hXQ : L1 ⊔ S ⊔ N1 ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    hXP.trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hL1Q : L1 ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    hL1P.trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hN1Q : N1 ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    hN1P.trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hRQ : R ≤ Q1 L1 L2 S := hstep.1.1
  have hLR : L < R := hstep.2.2.1
  have hXR : L1 ⊔ S ⊔ N1 ≤ Subgroup.normalizer (R : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.1
  have hXL : L1 ⊔ S ⊔ N1 ≤ Subgroup.normalizer (L : Set G) :=
    D14.le_normalizer_of_isNormalIn hstep.2.1
  have hRL : R ≤ Subgroup.normalizer (L : Set G) := hRQ.trans (hQX.trans hXL)
  have hchief : ∀ Y : Subgroup G, L ≤ Y → Y ≤ R →
      L1 ⊔ S ⊔ N1 ≤ Subgroup.normalizer (Y : Set G) → Y = L ∨ Y = R := by
    intro Y hLY hYR hXY
    exact hstep.2.2.2 Y ⟨hYR.trans hRQ, fun g hg y hy =>
      (Subgroup.mem_normalizer_iff.mp (hXY hg) y).mp hy⟩ hLY hYR
  have hQtriv : ∀ q ∈ Q1 L1 L2 S, ∀ r ∈ R, q * r * q⁻¹ * r⁻¹ ∈ L :=
    CFSG.GroupTheory.commutator_mem_of_chief hQ2 hQX hXQ (hQ2.to_le hRQ) hLR hXR hXL hRL hchief
  have hL1K : L1 ≤ Subgroup.normalizer ((N1 ⊔ Q1 L1 L2 S : Subgroup G) : Set G) :=
    le_normalizer_sup_of_commutator_mem hN1Q hL1Q fun l hl n hn => by
      have h := (pCoreOf 2 L1).inv_mem (hN1L n hn l hl)
      rw [show (n * l * n⁻¹ * l⁻¹)⁻¹ = l * n * l⁻¹ * n⁻¹ from by group] at h
      exact Hyp111.pCoreOf_le_pCoreOf_vertex hF h
  have hQK : Q1 L1 L2 S ≤ Subgroup.normalizer ((N1 ⊔ Q1 L1 L2 S : Subgroup G) : Set G) :=
    (le_sup_right : Q1 L1 L2 S ≤ N1 ⊔ Q1 L1 L2 S).trans Subgroup.le_normalizer
  have hLSK : L1 ⊔ S ≤ Subgroup.normalizer ((N1 ⊔ Q1 L1 L2 S : Subgroup G) : Set G) := by
    rw [hLS]
    exact sup_le hL1K hQK
  have hXK : L1 ⊔ S ⊔ N1 ≤ Subgroup.normalizer ((N1 ⊔ Q1 L1 L2 S : Subgroup G) : Set G) :=
    sup_le hLSK ((le_sup_left : N1 ≤ N1 ⊔ Q1 L1 L2 S).trans Subgroup.le_normalizer)
  by_cases hcase : ∀ x ∈ N1, ∀ r ∈ R, x * r * x⁻¹ * r⁻¹ ∈ L
  · exact Or.inl hcase
  ·
    right
    intro r hr hNr
    have hKT : N1 ⊔ Q1 L1 L2 S ≤
        CFSG.GroupTheory.commMemSubgroup (Subgroup.normalizer (L : Set G)) L le_rfl r := by
      refine sup_le ?_ ?_
      · intro x hx
        rw [CFSG.GroupTheory.mem_commMemSubgroup]
        exact ⟨hXL (hN1X hx), by simpa [commutatorElement_def] using hNr x hx⟩
      · intro q hq
        rw [CFSG.GroupTheory.mem_commMemSubgroup]
        exact ⟨hXL (hQX hq), by simpa [commutatorElement_def] using hQtriv q hq r hr⟩
    push Not at hcase
    obtain ⟨x, hxN, r₀, hr₀, hxr₀⟩ := hcase
    refine CFSG.GroupTheory.mem_of_commutator_mem_of_chief (N := L1 ⊔ S ⊔ N1)
      (K := N1 ⊔ Q1 L1 L2 S) (R₁ := R) (R₂ := L) (sup_le hN1X hQX) hXK hLR hXR hXL hRL
      hchief ⟨x, Subgroup.mem_sup_left hxN, r₀, hr₀, hxr₀⟩ hr ?_
    intro k hk
    have hk' := (CFSG.GroupTheory.mem_commMemSubgroup le_rfl r k).mp (hKT hk)
    simpa [commutatorElement_def] using hk'.2

end CFSG.Quasithin.Stroth.G5F

end
