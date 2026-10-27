module

public import CFSG.Milestones.ASVolI.C135.C136
public import CFSG.Milestones.ASVolI.C135.P4d
public import CFSG.Quasithin.Vol2.Ch4Sec3C135Holds
public import CFSG.Milestones.ASVolI.C135.P5

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open CFSG.ASVolI.ChC
open CFSG.Quasithin.H13.Ch4.C135 (slNat)
open scoped Pointwise

@[expose] def burnsideC135_AsC135ThreeOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (G₀ R₀ L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (α : ↥L →* ↥(StatedSL 3 F)),
    IsMSPair G₀ R₀ → L ∈ cComp G₀ → (G₀ : Set G) = (L : Set G) * (R₀ : Set G) →
    G₀ ≤ Subgroup.normalizer (L : Set G) → Fintype.card F = 2 → IsModO2Surj L α →
    G₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
    IsSumOfNaturalModulesVia L (centerOf (c134Q G₀ L)) ⊥ α false 1 →
    IsSumOfNaturalModulesVia L (c134Q G₀ L) (centerOf (c134Q G₀ L)) α true 2 →
      pCoreOf 2 G₀ = c134Q G₀ L

theorem burnsideC135_C_1_35_of_threeOne (h134 : burnsideC135_C134W)
    (hOne : burnsideC135_AsC135ThreeOne) : C_1_35 := by
  intro G _ _ X R L S n hMS hS ⟨F, _, _, hF, ⟨e⟩⟩ hCL hchief
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨i, hi, hci⟩ := burnsideC135_case_of_chief h134 hMS hF e (by norm_num) hchief
  have hi3 : i = 3 := burnsideC135_caseCount_eq_three hci
  subst hi3
  obtain ⟨⟨n', F', _, _, α', hF', hα', h1, h2⟩, -⟩ := hi
  have hnn : n = n' := burnsideC135_n_eq hF hF' e hα'
  rw [← hnn] at hF'
  have : CharP F' 2 := _root_.charP_of_card_eq_prime_pow hF'
  obtain ⟨hMSp, hL, hG⟩ := hMS
  have hLX : L ≤ X := MS93.le_of_coe_eq_mul_left hG
  have hXL : X ≤ Subgroup.normalizer (L : Set G) := by
    have h := MS93.le_normalizer_oddGen X
    rwa [← MS93.isMSPair_eq_oddGen hMSp hL hG] at h
  have hT : pCoreOf 2 X = c134Q X L := by
    by_cases hn : 2 ≤ n
    · exact CFSG.Quasithin.H13.Ch4.asC135Three_holds G X R L n F' α' hMSp hL hG hXL hn hF' hα'
        hCL h1 h2
    · have hn1 : n = 1 := by
        have := burnsideC135_one_le_n hF
        omega
      rw [hn1, pow_one] at hF'
      exact hOne G X R L F' α' hMSp hL hG hXL hF' hα' hCL h1 h2
  have hQO : pCoreOf 2 L = c134Q X L :=
    le_antisymm ((MS93.pCoreOf_le_pCoreOf_of_le_normalizer hLX hXL).trans hT.le)
      (MS93.commutator_le_pCoreOf hLX hXL)
  have hP : pCoreOf 2 X = pCoreOf 2 L := hT.trans hQO.symm
  have h1' := h1
  have h2' := h2
  rw [← hQO] at h1' h2'
  have hcomm : ∀ x ∈ pCoreOf 2 L, ∀ y ∈ pCoreOf 2 L,
      x * y * x⁻¹ * y⁻¹ ∈ centerOf (pCoreOf 2 L) := fun x hx y hy =>
    burnsideC135_comm_mem_U h2' hx hy
  obtain ⟨W₁, W₂, βU, β₁, β₂, hD⟩ := burnsideC135_dualSplit_of_case3 hα' h1' h2'
  refine ⟨⟨⟨3 * n, 6 * n, burnsideC135_isSpecial hα' hF' h1' h2'⟩, F', inferInstance,
    inferInstance, hF', W₁, W₂, slNat α', βU, β₁, β₂,
    burnsideC135_dualSplit_of_dsg hD (burnsideC135_slNat_ker hα')⟩, ?_, hP, ?_,
    burnsideC135_part5 hMSp hL hG hXL hS hα' hQO hP h1 h2⟩
  ·
    intro F'' _ _ hF'' V₁ V₂ γ γU γ₁ γ₂ hD''
    have : CharP F'' 2 := _root_.charP_of_card_eq_prime_pow hF''
    have hD' := burnsideC135_dsg_of_dualSplit hD''
    obtain ⟨hE₁, hE₂⟩ := burnsideC135_isE2_W hD' hF''
    refine ⟨hE₁, hE₂, fun w hw => ⟨?_, fun v => ?_⟩⟩
    · rw [burnsideC135_relIndex hD' hcomm w hw, hF'']
    · constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : (x : G) * w = w * x := Subgroup.mem_centralizer_singleton_iff.mp hx
        exact (burnsideC135_commute_iff hD' hcomm w hw x).mp hx'.symm
      · rintro ⟨c, rfl⟩
        obtain ⟨x, hx⟩ := hD'.dual₂_onto
          (Multiplicative.ofAdd (c • Multiplicative.toAdd (γ₁ w)))
        refine ⟨x, ?_, by rw [hx]; rfl⟩
        have hxw := (burnsideC135_commute_iff hD' hcomm w hw x).mpr ⟨c, by rw [hx]; rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.mpr hxw.symm
  ·
    obtain ⟨hsq₁, -⟩ := burnsideC135_W_sq hD
    refine ⟨W₁, ⟨(hD.le_Q₁.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).trans hLX,
      ⟨⟨⟨fun a b => Subtype.ext (burnsideC135_comm_of_sq hsq₁ a.2 b.2)⟩⟩, fun x hx => by
        rw [sq]; exact hsq₁ x hx⟩, fun B hBX hB => ?_⟩, ?_⟩
    · rw [burnsideC135_card_dual hD hD.le₁ hD.dual₁_onto hD.dual₁_ker]
      exact burnsideC135_card_elemAb_le hF' hMSp hG hα' hLX hXL hQO hP h1 h2 hBX hB
    · rw [burnsideC135_card_dual hD hD.le₁ hD.dual₁_onto hD.dual₁_ker, hF', ← pow_mul, mul_comm]

end CFSG.ASVolI

end
