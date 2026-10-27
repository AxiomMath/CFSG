module

public import CFSG.Quasithin.Vol2.Ch12Sec2E22BorelLiftLie
public import CFSG.Quasithin.Background.E6TorusCover
public import CFSG.Quasithin.H13.KGFact22TorusFacts

public section

namespace CFSG.Quasithin.Gap6R2.L3

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem comm_mem_of_sup {C R : Subgroup G} (hCR : C ≤ Subgroup.normalizer (R : Set G))
    (hC : IsMulCommutative ↥C) {a b : G} (ha : a ∈ C ⊔ R) (hb : b ∈ C ⊔ R) :
    a * b * a⁻¹ * b⁻¹ ∈ R := by
  classical
  have hW : C ⊔ R ≤ Subgroup.normalizer (R : Set G) := sup_le hCR Subgroup.le_normalizer
  have hn : (R.subgroupOf (C ⊔ R)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hW
  set π : ↥(C ⊔ R) →* ↥(C ⊔ R) ⧸ R.subgroupOf (C ⊔ R) := QuotientGroup.mk' _ with hπ
  have hdec : ∀ x : G, x ∈ C ⊔ R → ∃ c ∈ C, ∃ r ∈ R, x = c * r := by
    intro x hx
    have : x ∈ ((C ⊔ R : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right C R hCR] at this
    obtain ⟨c, hc, r, hr, hxe⟩ := Set.mem_mul.mp this
    exact ⟨c, hc, r, hr, hxe.symm⟩
  have hle : C ≤ C ⊔ R := le_sup_left
  have hπc : ∀ x : ↥(C ⊔ R), ∃ c : ↥C, π x = π (Subgroup.inclusion hle c) := by
    intro x
    obtain ⟨c, hc, r, hr, hxe⟩ := hdec x x.2
    refine ⟨⟨c, hc⟩, ?_⟩
    have hr' : (⟨r, Subgroup.mem_sup_right hr⟩ : ↥(C ⊔ R)) ∈ R.subgroupOf (C ⊔ R) := hr
    have : x = Subgroup.inclusion hle ⟨c, hc⟩ * ⟨r, Subgroup.mem_sup_right hr⟩ :=
      Subtype.ext hxe
    have hπr : π ⟨r, Subgroup.mem_sup_right hr⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hr'
    rw [this, map_mul, hπr, mul_one]
  obtain ⟨c₁, h₁⟩ := hπc ⟨a, ha⟩
  obtain ⟨c₂, h₂⟩ := hπc ⟨b, hb⟩
  have hcomm : π (Subgroup.inclusion hle c₁) * π (Subgroup.inclusion hle c₂) =
      π (Subgroup.inclusion hle c₂) * π (Subgroup.inclusion hle c₁) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, isMulCommutative_iff.mp hC c₁ c₂]
  have h1 : π (⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h₁, h₂, hcomm]
    group
  have h2 := (QuotientGroup.eq_one_iff _).mp h1
  exact Subgroup.mem_subgroupOf.mp h2

omit [Finite G] in
theorem oddComm_of_borelLift {H T MH : Subgroup G} {n : ℕ} (hTM : T ≤ MH) (hMH : MH ≤ H)
    (hBL : E2.E22BorelLift H T MH n) :
    ∀ a ∈ MH, Odd (orderOf a) → ∀ b ∈ MH, Odd (orderOf b) →
      a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 MH := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, R, hRT, hR2, hRn, ⟨C, hCM, hCodd, k, hk⟩, hall⟩ := hBL
  obtain ⟨-, hINC, hCc, -⟩ := hall C hCM hCodd ⟨k, hk⟩
  have hRP : R ≤ pCoreOf 2 MH := le_pCoreOf_of_le_normalizer 2 (hRT.trans hTM) hRn hR2
  intro a ha hoa b hb hob
  have haW : a ∈ C ⊔ R := hINC ⟨ha, mem_oTwoUpper_of_odd (hMH ha) hoa⟩
  have hbW : b ∈ C ⊔ R := hINC ⟨hb, mem_oTwoUpper_of_odd (hMH hb) hob⟩
  exact hRP (comm_mem_of_sup (hCM.trans hRn) hCc haW hbW)

theorem oddComm_of_lie {H T MH K : Subgroup G}
    (hmin : MinParabolic H T MH) (hK : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hL : E2.E22LieCases H T MH K) :
    ∀ a ∈ MH, Odd (orderOf a) → ∀ b ∈ MH, Odd (orderOf b) →
      a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 MH := by
  obtain ⟨n, -, hBL⟩ := E2.e22BorelLift_lie
    (E2.e22TorusCover_of_facts H13.e22TorusFacts_holds) hmin hK hHK hL
  exact oddComm_of_borelLift hmin.le hmin.maximal.1.le hBL

end CFSG.Quasithin.Gap6R2.L3
