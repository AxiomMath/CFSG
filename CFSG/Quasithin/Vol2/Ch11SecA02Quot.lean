module

public import CFSG.Quasithin.Vol2.Ch11SecANat
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch11SecABasicV

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

theorem le_center_of_normal_ne_top {X : Type*} [Group X] (hQ : CFSG.IsQuasisimple X)
    {N : Subgroup X} [hN : N.Normal] (hNt : N ≠ ⊤) : N ≤ Subgroup.center X := by
  obtain ⟨hperf, hsimp, -⟩ := hQ
  set π := QuotientGroup.mk' (Subgroup.center X)
  have hnorm : (N.map π).Normal := hN.map π (QuotientGroup.mk'_surjective _)
  have := hsimp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with hb | ht
  · intro x hx
    have : π x = 1 := by
      have := Subgroup.mem_map_of_mem π hx
      rw [hb, Subgroup.mem_bot] at this
      exact this
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  · exfalso
    apply hNt
    have hdec : ∀ a : X, ∃ m ∈ N, m⁻¹ * a ∈ Subgroup.center X := by
      intro a
      have : π a ∈ N.map π := by rw [ht]; trivial
      obtain ⟨m, hm, hma⟩ := this
      refine ⟨m, hm, ?_⟩
      rw [← QuotientGroup.eq]
      exact hma
    rw [eq_top_iff, ← hperf.commutator_eq_top, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨m₁, hm₁, hz₁⟩ := hdec a
    obtain ⟨m₂, hm₂, hz₂⟩ := hdec b
    have ha : a = m₁ * (m₁⁻¹ * a) := by group
    have hb : b = m₂ * (m₂⁻¹ * b) := by group
    set z₁ := m₁⁻¹ * a
    set z₂ := m₂⁻¹ * b
    have hc₁ := Subgroup.mem_center_iff.mp hz₁
    have hc₂ := Subgroup.mem_center_iff.mp hz₂
    have e : ⁅a, b⁆ = ⁅m₁, m₂⁆ := by
      rw [ha, hb, commutatorElement_def, commutatorElement_def]
      calc m₁ * z₁ * (m₂ * z₂) * (m₁ * z₁)⁻¹ * (m₂ * z₂)⁻¹
          = m₁ * (z₁ * m₂) * z₂ * z₁⁻¹ * m₁⁻¹ * z₂⁻¹ * m₂⁻¹ := by group
        _ = m₁ * (m₂ * z₁) * z₂ * z₁⁻¹ * m₁⁻¹ * z₂⁻¹ * m₂⁻¹ := by rw [hc₁ m₂]
        _ = m₁ * m₂ * (z₁ * z₂ * z₁⁻¹) * m₁⁻¹ * z₂⁻¹ * m₂⁻¹ := by group
        _ = m₁ * m₂ * z₂ * m₁⁻¹ * z₂⁻¹ * m₂⁻¹ := by
          rw [show z₁ * z₂ * z₁⁻¹ = z₂ by rw [← hc₁ z₂]; group]
        _ = m₁ * m₂ * (z₂ * m₁⁻¹) * z₂⁻¹ * m₂⁻¹ := by group
        _ = m₁ * m₂ * (m₁⁻¹ * z₂) * z₂⁻¹ * m₂⁻¹ := by rw [hc₂ m₁⁻¹]
        _ = m₁ * m₂ * m₁⁻¹ * m₂⁻¹ := by group
    rw [e]
    exact N.mul_mem (N.mul_mem (N.mul_mem hm₁ hm₂) (N.inv_mem hm₁)) (N.inv_mem hm₂)

theorem odd_card_of_le_center {X : Type*} [Group X] [Finite X] (hO : CFSG.pCore 2 X = ⊥)
    {N : Subgroup X} (hN : N ≤ Subgroup.center X) : Odd (Nat.card N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 h2
  have hxc : (x : X) ∈ Subgroup.center X := hN x.2
  have hnorm : (Subgroup.zpowers (x : X)).Normal := by
    constructor
    intro y hy g
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hk := Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hxc k) g
    rw [hk, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ k
  have hp : IsPGroup 2 (Subgroup.zpowers (x : X)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, orderOf_submonoid, hx, pow_one]
  have hle : Subgroup.zpowers (x : X) ≤ CFSG.pCore 2 X := by
    exact CFSG.LieType.BorelTits.le_pCore 2 hnorm hp
  rw [hO, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  have : orderOf x = 1 := by
    rw [← orderOf_submonoid, hle, orderOf_one]
  omega

variable {G : Type} [Group G]

theorem autOn_normal_subgroupOf {A B V : Subgroup G} (hBA : B ≤ Subgroup.normalizer (A : Set G)) :
    ((autOn A V).subgroupOf (autOn B V)).Normal := by
  constructor
  rintro ⟨x, hxB⟩ hx ⟨g, hg⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨a, haA, haV, rfl⟩ := mem_autOn_iff.mp hx
  obtain ⟨b, hbB, hbV, rfl⟩ := mem_autOn_iff.mp hg
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← conjV_inv, ← conjV_mul, ← conjV_mul]
  refine conjV_mem_autOn ?_ _
  have := (Subgroup.mem_normalizer_iff.mp (hBA hbB) a).mp haA
  simpa [mul_assoc] using this

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem pCoreOf_autOn_eq_bot (h8 : Ch10.TmpL6_3_2_2_eight) (h : Hyp11 G T L I n) :
    pCoreOf 2 (autOn L (fsuV T I)) = ⊥ := by
  obtain ⟨hVX, hR, -⟩ := h8 G T L I h.fsu
  rw [fsuL0_eq h] at hVX hR
  have h1 := InternalSec.pCoreOf_autOn_eq_bot_of_isPrimeReduced hVX hR
  have h2 := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2
    (autOn L (fsuV T I)) (autOn (L ⊔ T) (fsuV T I))
    (Subgroup.map_mono fun _ hx => Subgroup.mem_sup_left hx)
    (autOn_normal_subgroupOf (sup_le Subgroup.le_normalizer h.normal))
  rw [h1] at h2
  exact le_bot_iff.mp h2

theorem not_le_centralizer_fsuV (h : Hyp11 G T L I n) :
    ¬ L ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  intro hL
  have hlt := h.fsu.irrPlus.2.2.2.2.1
  rw [show conjClosure L T = L from fsuL0_eq h] at hlt
  have hI : I ≤ Subgroup.centralizer (L : Set G) :=
    (le_conjClosure I T).trans (Subgroup.le_centralizer_iff.mp hL)
  exact lt_irrefl I (lt_of_le_of_lt (le_inf le_rfl hI) hlt)

theorem exists_quot_hom (h8 : Ch10.TmpL6_3_2_2_eight) (h : Hyp11 G T L I n) :
    ∃ f : ↥L ⧸ CFSG.pCore 2 ↥L →* ↥(autOn L (fsuV T I)), Function.Surjective f ∧
      f.ker ≤ Subgroup.center _ ∧ Odd (Nat.card f.ker) := by
  have hLV := L_le_normalizer_fsuV h
  have hle := InternalSec.pCore_le_ker_autOnHom hLV (pCoreOf_autOn_eq_bot h8 h)
  set f := QuotientGroup.lift _ (InternalSec.autOnHom hLV) hle
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨l, rfl⟩ := InternalSec.autOnHom_surjective hLV y
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hker : f.ker ≠ ⊤ := by
    intro htop
    apply InternalSec.ker_autOnHom_ne_top hLV (not_le_centralizer_fsuV h)
    rw [eq_top_iff]
    intro l _
    have : (QuotientGroup.mk l : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ f.ker := by rw [htop]; trivial
    exact this
  have hZ := le_center_of_normal_ne_top h.fsu.quasisimple hker
  refine ⟨f, hf, hZ, odd_card_of_le_center ?_ hZ⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot

end CFSG.Quasithin.Vol2.Ch11.SecA
