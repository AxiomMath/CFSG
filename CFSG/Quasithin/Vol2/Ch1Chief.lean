module

public import CFSG.Quasithin.Vol2.Ch1Inputs
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Background.A3Structure312Quotient
public import CFSG.Quasithin.Background.A3Structure36ABasic
public import CFSG.Quasithin.Vol2.Ch1ModO2
public import CFSG.Quasithin.Vol2.Ch1Prop121

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

section TwoSection

theorem exists_not_two_power_of_simple (S : Type*) [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) : ∃ s : S, ∀ k : ℕ, s ^ 2 ^ k ≠ 1 := by
  by_contra h
  push Not at h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 S := h
  have hnil : Group.IsNilpotent S := hp.isNilpotent
  have hsolv : Group.IsSolvable S := inferInstance
  obtain ⟨a, b, hab⟩ := hna
  have hnt : Nontrivial S := ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial S
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h1 | h1
  · have hc : IsMulCommutative S := (commutator_eq_bot_iff S).mp h1
    exact hab (hc.is_comm.comm a b)
  · rw [h1] at hlt
    exact lt_irrefl _ hlt

variable {Y : Type*} [Group Y] [Finite Y]

theorem commutator_le_of_two_section {R F A B : Subgroup Y} [hFn : F.Normal] [hRn : R.Normal]
    [hAn : A.Normal] [hBn : B.Normal] (hFodd : ∀ x ∈ F, Odd (orderOf x))
    (hidx : F.relIndex R ≤ 2) [IsSimpleGroup (Y ⧸ R)] (hna : ∃ a b : Y ⧸ R, a * b ≠ b * a)
    (hBA : B ≤ A) (h2 : ∀ a ∈ A, ∃ k : ℕ, a ^ 2 ^ k ∈ B) : ⁅A, (⊤ : Subgroup Y)⁆ ≤ B := by
  have hFA : ∀ x ∈ F, x ∈ A → x ∈ B := by
    intro x hxF hxA
    obtain ⟨k, hk⟩ := h2 x hxA
    have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (hFodd x hxF))
    exact Subgroup.zpowers_le.mpr hk (A4.mem_zpowers_pow_of_coprime hcop)
  let ρ : Y →* Y ⧸ R := QuotientGroup.mk' R
  have hρ : Function.Surjective ρ := QuotientGroup.mk'_surjective R
  have hsplit : ∀ a ∈ A, ∃ d ∈ A, d ∈ R ∧ ∃ b ∈ B, a = d * b := by
    intro a ha
    by_cases hBR : B ≤ R
    · by_cases hAR : A ≤ R
      · exact ⟨a, ha, hAR ha, 1, B.one_mem, (mul_one a).symm⟩
      · exfalso
        have hAmap : (A.map ρ).Normal := Subgroup.Normal.map hAn ρ hρ
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.map ρ) with h | h
        · apply hAR
          intro x hx
          have : ρ x = 1 := Subgroup.mem_bot.mp (h ▸ Subgroup.mem_map_of_mem ρ hx)
          exact (QuotientGroup.eq_one_iff x).mp this
        · obtain ⟨s, hs⟩ := exists_not_two_power_of_simple (Y ⧸ R) hna
          have hsA : s ∈ A.map ρ := h ▸ Subgroup.mem_top s
          obtain ⟨a', ha', rfl⟩ := hsA
          obtain ⟨k, hk⟩ := h2 a' ha'
          apply hs k
          rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact hBR hk
    · have hBmap : (B.map ρ).Normal := Subgroup.Normal.map hBn ρ hρ
      have htop : B.map ρ = ⊤ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (B.map ρ) with h | h
        · exfalso
          apply hBR
          intro x hx
          have : ρ x = 1 := Subgroup.mem_bot.mp (h ▸ Subgroup.mem_map_of_mem ρ hx)
          exact (QuotientGroup.eq_one_iff x).mp this
        · exact h
      have : ρ a ∈ B.map ρ := htop ▸ Subgroup.mem_top _
      obtain ⟨b, hb, hba⟩ := this
      refine ⟨a * b⁻¹, A.mul_mem ha (A.inv_mem (hBA hb)), ?_, b, hb, by group⟩
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have hba' : (b : Y ⧸ R) = a := hba
      rw [hba', mul_inv_cancel]
  have hcomm : ∀ d ∈ A, d ∈ R → ∀ y : Y, ⁅d, y⁆ ∈ B := by
    intro d hdA hdR y
    by_cases hdF : d ∈ F
    · have hdB : d ∈ B := hFA d hdF hdA
      have : ⁅d, y⁆ = d * (y * d⁻¹ * y⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact B.mul_mem hdB (hBn.conj_mem d⁻¹ (B.inv_mem hdB) y)
    · have hne : (F.subgroupOf R).index ≠ 1 := by
        intro h1
        rw [Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top] at h1
        exact hdF (h1 hdR)
      have hpos : (F.subgroupOf R).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have hidx2 : (F.subgroupOf R).index = 2 := by
        have : (F.subgroupOf R).index ≤ 2 := hidx
        omega
      have hyd : y * d * y⁻¹ ∈ R := hRn.conj_mem d hdR y
      have hnot₁ : (⟨d, hdR⟩ : ↥R)⁻¹ ∉ F.subgroupOf R := by
        intro h
        exact hdF (by simpa using (Subgroup.mem_subgroupOf.mp (F.subgroupOf R |>.inv_mem h)))
      have hnot₂ : (⟨y * d * y⁻¹, hyd⟩ : ↥R) ∉ F.subgroupOf R := by
        intro h
        have h' : y * d * y⁻¹ ∈ F := Subgroup.mem_subgroupOf.mp h
        apply hdF
        have := hFn.conj_mem _ h' y⁻¹
        simpa [mul_assoc] using this
      have hprod : (⟨d, hdR⟩ : ↥R)⁻¹ * ⟨y * d * y⁻¹, hyd⟩ ∈ F.subgroupOf R :=
        (Subgroup.mul_mem_iff_of_index_two hidx2).mpr ⟨fun h => absurd h hnot₁,
          fun h => absurd h hnot₂⟩
      have hfF : d⁻¹ * (y * d * y⁻¹) ∈ F := Subgroup.mem_subgroupOf.mp hprod
      have hfA : d⁻¹ * (y * d * y⁻¹) ∈ A :=
        A.mul_mem (A.inv_mem hdA) (hAn.conj_mem d hdA y)
      have hfB := hFA _ hfF hfA
      have : ⁅d, y⁆ = d * (d⁻¹ * (y * d * y⁻¹))⁻¹ * d⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact hBn.conj_mem _ (B.inv_mem hfB) d
  refine Subgroup.commutator_le.mpr fun a ha y _ => ?_
  obtain ⟨d, hdA, hdR, b, hb, rfl⟩ := hsplit a ha
  have : ⁅d * b, y⁆ = d * ⁅b, y⁆ * d⁻¹ * ⁅d, y⁆ := by
    simp only [commutatorElement_def]; group
  rw [this]
  refine B.mul_mem ?_ (hcomm d hdA hdR y)
  have hby : ⁅b, y⁆ ∈ B := by
    have : ⁅b, y⁆ = b * (y * b⁻¹ * y⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact B.mul_mem hb (hBn.conj_mem b⁻¹ (B.inv_mem hb) y)
  exact hBn.conj_mem _ hby d

end TwoSection

section Application

variable {G : Type} [Group G] [Finite G]

theorem lemma_1_2_1_four (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h36 : A36ForSQTK) {H L : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) (hL : L ∈ cComp H) : A36Conclusion (modO2Image H L) :=
  (h36 _ (sqtkHyp_quotient_of_pCoreOf_ne_bot hK hs hnab hH) _ (modO2Image_mem_cComp hL)).1

theorem lemma_1_2_1_four_strong (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h36 : A36ForSQTK) {H L : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) (hL : L ∈ cComp H) : A36Strong (modO2Image H L) :=
  h36 _ (sqtkHyp_quotient_of_pCoreOf_ne_bot hK hs hnab hH) _ (modO2Image_mem_cComp hL)

theorem noncentralTwoChiefFactorsInO2_of_a3 {H L : Subgroup G}
    (h36 : A36Statement (↥H ⧸ CFSG.pCore 2 ↥H)) (hL : L ∈ cComp H) :
    NoncentralTwoChiefFactorsInO2 L := by
  intro A B hAB
  obtain ⟨hOB, hBA, hAL, hLA, hLB, -, h2⟩ := hAB
  have hLb := modO2Image_mem_cComp hL
  obtain ⟨-, ⟨hFO, -, hrad, -⟩, -⟩ := h36 _ hLb
  obtain ⟨hsimple, hna⟩ := A36A.simple_quotient_of_mem_cComp hLb
  obtain ⟨ψ, hψ, hker⟩ := exists_modO2_surjection hL
  have := hsimple
  have hBL : B ≤ L := hBA.le.trans hAL
  have hAn : (A.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAL).mpr hLA
  have hBn : (B.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBL).mpr hLB
  have hAn' : ((A.subgroupOf L).map ψ).Normal := Subgroup.Normal.map hAn ψ hψ
  have hBn' : ((B.subgroupOf L).map ψ).Normal := Subgroup.Normal.map hBn ψ hψ
  have hFodd : ∀ x ∈ CFSG.fittingSubgroup ↥(modO2Image H L), Odd (orderOf x) := by
    intro x hx
    have hx' : x ∈ CFSG.oddCore ↥(modO2Image H L) := hFO ▸ hx
    exact Odd.of_dvd_nat (A312.odd_card_oddCore _) (Subgroup.orderOf_dvd_natCard _ hx')
  have hidx : (CFSG.fittingSubgroup ↥(modO2Image H L)).relIndex
      (CFSG.solvableRadical ↥(modO2Image H L)) ≤ 2 := by
    rcases hrad with ⟨-, hr⟩ | ⟨-, hFR, -⟩
    · exact hr.le
    · rw [hFR, Subgroup.relIndex_self]
      norm_num
  have hBA' : (B.subgroupOf L).map ψ ≤ (A.subgroupOf L).map ψ :=
    Subgroup.map_mono fun x hx => hBA.le hx
  have h2' : ∀ a ∈ (A.subgroupOf L).map ψ, ∃ k : ℕ, a ^ 2 ^ k ∈ (B.subgroupOf L).map ψ := by
    rintro _ ⟨a', ha', rfl⟩
    obtain ⟨k, hk⟩ := h2 (a' : G) ha'
    refine ⟨k, a' ^ 2 ^ k, ?_, map_pow ψ a' _⟩
    show ((a' ^ 2 ^ k : ↥L) : G) ∈ B
    simpa using hk
  have hZ := commutator_le_of_two_section hFodd hidx hna hBA' h2'
  have hker' : CFSG.pCore 2 ↥L ≤ B.subgroupOf L := by
    intro x hx
    apply hOB
    exact ⟨x, hx, rfl⟩
  refine Subgroup.commutator_le.mpr fun a ha y hy => ?_
  have hmem := hZ (Subgroup.commutator_mem_commutator
    (Subgroup.mem_map_of_mem ψ (show (⟨a, hAL ha⟩ : ↥L) ∈ A.subgroupOf L from ha))
    (Subgroup.mem_top (ψ ⟨y, hy⟩)))
  rw [← map_commutatorElement] at hmem
  obtain ⟨b', hb', hb'e⟩ := hmem
  have hk : b'⁻¹ * ⁅(⟨a, hAL ha⟩ : ↥L), ⟨y, hy⟩⁆ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hb'e, inv_mul_cancel]
  rw [hker] at hk
  have hk' := hker' hk
  have hc : ⁅(⟨a, hAL ha⟩ : ↥L), ⟨y, hy⟩⁆ ∈ B.subgroupOf L := by
    have := (B.subgroupOf L).mul_mem hb' hk'
    simpa using this
  have hcG : ((⁅(⟨a, hAL ha⟩ : ↥L), ⟨y, hy⟩⁆ : ↥L) : G) ∈ B := hc
  simpa [commutatorElement_def] using hcG

theorem noncentralTwoChiefFactorsInO2_of_a36 (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h36 : A36ForSQTK) {H L : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) (hL : L ∈ cComp H) : NoncentralTwoChiefFactorsInO2 L :=
  noncentralTwoChiefFactorsInO2_of_a3
    (h36 _ (sqtkHyp_quotient_of_pCoreOf_ne_bot hK hs hnab hH)) hL

theorem lemma_1_2_10_of_a36 (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h36 : A36ForSQTK) (T : Sylow 2 G) {H L : Subgroup G}
    (hH : InH (T : Subgroup G) H) (hL : L ∈ cComp H) :
    List.TFAE [quasithinIsFaithfulLocal (T : Subgroup G) L,
      ∃ V, IsTwoReducedIn H V ∧ ⁅V, L⁆ ≠ ⊥, ⁅twoReducedJoin H, L⁆ ≠ ⊥] :=
  lemma_1_2_10 hK.2.1 T hH hL (noncentralTwoChiefFactorsInO2_of_a36 hK hs hnab h36 hH.2 hL)

end Application

end CFSG.Quasithin
