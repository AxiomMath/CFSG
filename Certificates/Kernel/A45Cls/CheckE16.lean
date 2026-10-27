module

public import Certificates.Kernel.A45Cls.Kit
public import Certificates.Kernel.A45Cls.Checks9
public import CFSG.Certificates.Kernel.A45Cls.E16WalkSound
public import Certificates.Data.OmegaInv

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbFind CFSG.KC.BfsPin CFSG.KC.EnumSound
  CFSG.KC.A45Cls CFSG.KC.E16Walk CFSG.KC.SylowReps Subgroup
  CFSG.ComponentClassification.CatFactsSmall.PSp43 Certificates.OmegaInv

local notation "P45" => Equiv.Perm (Fin 45)

theorem exists_conj_le_sylS {R : Subgroup P45} (hRA : R ≤ A)
    (hp : IsPGroup 2 R) : ∃ g ∈ A, ∀ x ∈ R, g⁻¹ * x * g ∈ sylS := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q' : Subgroup A := sylS.subgroupOf A
  have hQ'card : Nat.card Q' = 2 ^ (Nat.card A).factorization 2 := by
    rw [card_A, show (51840 : ℕ) = 2 ^ 7 * 405 by norm_num,
      pow_factorization_eq Nat.prime_two (by norm_num),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe sylS_le).toEquiv, card_sylS]
    norm_num
  let S0 : Sylow 2 A := Sylow.ofCard Q' hQ'card
  have hpR' : IsPGroup 2 (R.subgroupOf A) := hp.of_equiv (Subgroup.subgroupOfEquivOfLe hRA).symm
  obtain ⟨S, hS⟩ := hpR'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A S0 S
  refine ⟨g, g.2, fun x hx => ?_⟩
  have hxS : (⟨x, hRA hx⟩ : A) ∈ (S : Subgroup A) := hS (Subgroup.mem_subgroupOf.2 hx)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxS
  obtain ⟨y, hy, hyx⟩ := hxS
  have hy' : y ∈ Q' := by
    have e : (S0 : Subgroup A) = Q' := Sylow.coe_ofCard _ _
    rwa [← e]
  have e : g⁻¹ * ⟨x, hRA hx⟩ * g = y := by
    rw [← hyx, MulAut.smul_def, MulAut.conj_apply]
    group
  have e' : (g : P45)⁻¹ * x * g = y := congrArg Subtype.val e
  rw [e']
  exact hy'

theorem e16_sylS {V : Subgroup P45} (hV : V ≤ sylS) (hV16 : Nat.card V = 16)
    (hsq : ∀ x ∈ V, x * x = 1) :
    ((∀ x ∈ V, fixC x = 45 ∨ fixC x = 13 ∨ fixC x = 5) ∨ ∃ x ∈ V, fixC x = 15) ∧
      ∀ F : Finset P45, (∀ x ∈ F, x ∈ V ∧ fixC x = 15) → F.card ≤ 4 := by
  have hN : SY.N = 128 := orders.2.2.2.2.2.2.2.2.1
  have him : CFSG.KD.E16W.invMask < 2 ^ SY.N := by
    rw [hN]
    decide
  have hG : Nat.card sylS = SY.N := by rw [hN, card_sylS]
  have hT : ∀ y ∈ sylS, ∃ i < SY.N, PRep 45 6 (SY.T i) y := by
    rw [hN]
    exact sylS_facts.2
  exact e16_sound hG hT him ce16inv ce16tab ce16full ce16pos ce16adj ce16nodes2 ce16nodes3
    ce16nodes4 ce16par2 ce16par3 ce16par4 ce16compl1 ce16compl2 ce16compl3 ce16fix ce16good hV
    hV16 hsq

theorem omegaCE16_model :
    ∀ S : Subgroup P45, S ≤ QA45.originalSubgroup → Nat.card S = 16 → (∀ x ∈ S, x * x = 1) →
      ((∀ x ∈ S, fixCnt x = 45 ∨ fixCnt x = 13 ∨ fixCnt x = 5) ∨ ∃ x ∈ S, fixCnt x = 15) ∧
        ∀ F : Finset P45, (∀ x ∈ F, x ∈ S ∧ fixCnt x = 15) → F.card ≤ 4 := by
  intro S hS hcard hsq
  have hp : IsPGroup 2 S := IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num)
  obtain ⟨g, -, hg⟩ := exists_conj_le_sylS hS hp
  let V : Subgroup P45 := S.map (MulAut.conj g⁻¹).toMonoidHom
  have hmem : ∀ x, x ∈ V ↔ ∃ y ∈ S, g⁻¹ * y * g = x := by
    intro x
    simp [V, Subgroup.mem_map, MulAut.conj_apply]
  have hfix : ∀ y : P45, fixC (g⁻¹ * y * g) = fixCnt y := by
    intro y
    have h := fixC_conj y g⁻¹
    rw [inv_inv] at h
    exact h
  have hVs : V ≤ sylS := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (hmem x).1 hx
    exact hg y hy
  have hV16 : Nat.card V = 16 := by
    rw [← hcard]
    exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hVsq : ∀ x ∈ V, x * x = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (hmem x).1 hx
    calc g⁻¹ * y * g * (g⁻¹ * y * g) = g⁻¹ * (y * y) * g := by group
      _ = 1 := by rw [hsq y hy]; group
  obtain ⟨hcases, hle⟩ := e16_sylS hVs hV16 hVsq
  have hinj : Function.Injective fun x : P45 => g⁻¹ * x * g := fun x y h => by
    simpa using h
  refine ⟨?_, fun F hF => ?_⟩
  · rcases hcases with h | ⟨x, hx, hx15⟩
    · left
      intro x hx
      rw [← hfix]
      exact h _ ((hmem _).2 ⟨x, hx, rfl⟩)
    · right
      obtain ⟨y, hy, rfl⟩ := (hmem x).1 hx
      exact ⟨y, hy, by rw [← hfix]; exact hx15⟩
  · rw [← Finset.card_image_of_injective F hinj]
    refine hle _ fun x hx => ?_
    obtain ⟨y, hyF, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨hyS, hy15⟩ := hF y hyF
    exact ⟨(hmem _).2 ⟨y, hyS, rfl⟩, by rw [hfix]; exact hy15⟩

end CertificateChecks.KernelA45

end
