module

public import CFSG.Quasithin.EmptyFaithful.SBd5Dec
public import CFSG.Quasithin.EmptyFaithful.SBd5Nat
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

namespace SBd5

section Packaged

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem act_surj {F : Type} [Field F] {L : Subgroup G}
    {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : Function.Surjective α)
    (g : Matrix.SpecialLinearGroup (Fin 3) F) :
    ∃ l : ↥L, ((α l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) := by
  obtain ⟨l, hl⟩ := hα (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F g)
  refine ⟨l, ?_⟩
  rw [hl]
  rfl

omit [Finite G] in
theorem exists_trivial_comm {F : Type} [Field F] {L : Subgroup G}
    {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : IsModO2Surj L α) {y : G}
    (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyc : ∀ x ∈ L, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 L) (l : ↥L) :
    ∃ o : ↥L, (o : G) = y * l * y⁻¹ * (l : G)⁻¹ ∧
      ((α o : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
  have h1 : y * (l : G) * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyL l).mp l.2
  have h2 : y * (l : G) * y⁻¹ * (l : G)⁻¹ ∈ L := L.mul_mem h1 (L.inv_mem l.2)
  refine ⟨⟨_, h2⟩, rfl, ?_⟩
  have h3 : y * (l : G) * y⁻¹ * (l : G)⁻¹ ∈ pCoreOf 2 L := by
    have := (pCoreOf 2 L).inv_mem (hyc l l.2)
    have e : ((l : G) * y * (l : G)⁻¹ * y⁻¹)⁻¹ = y * (l : G) * y⁻¹ * (l : G)⁻¹ := by group
    rwa [e] at this
  obtain ⟨x, hx, hxo⟩ := Subgroup.mem_map.mp h3
  have hxeq : x = ⟨_, h2⟩ := Subtype.ext hxo
  have hker : (⟨_, h2⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
    rwa [← hxeq]
  have hker' : (⟨_, h2⟩ : ↥L) ∈ α.ker := by rw [hα.2]; exact hker
  have : α ⟨_, h2⟩ = 1 := hker'
  rw [this]
  rfl

omit [Finite G] in
theorem card_eq_two_of_modO2Surj {L : Subgroup G} (hq : IsLnTwoQuot L 3) {n : ℕ} {F : Type}
    [Field F] [Fintype F] (hFc : Fintype.card F = 2 ^ n)
    {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : IsModO2Surj L α) :
    Fintype.card F = 2 := by
  have h168 := card_quot_of_isLnTwoQuot hq
  have hq' := card_quot_of_surj_ker' hα.1 hα.2
  rw [h168] at hq'
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) = 168 := by
    rw [Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).toEquiv]
    exact hq'.symm
  have h2 := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := F) (n := 3)
    (by norm_num)
  have hF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hFc]
  rw [hSL, hF, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)] at h2
  have hn : n ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have hdvd : (2 ^ n) ^ (3 * (3 - 1) / 2) ∣ 168 := by
      rw [h2]
      exact Dvd.intro (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) (by ring)
    have h1 : 2 ^ 9 ≤ (2 ^ n) ^ (3 * (3 - 1) / 2) := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hn1 : 1 ≤ n := by
    by_contra hcon
    push Not at hcon
    have : n = 0 := by omega
    subst this
    have := Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial F)
    omega
  interval_cases n
  · rw [hFc]; norm_num
  · exfalso
    norm_num at h2

omit [Finite G] in
theorem kc_of_module {L Z A : Subgroup G} {y : G} {k n : ℕ} (hk : k = 1 ∨ k = 2) {F : Type}
    [Field F] [Fintype F] (hFc : Fintype.card F = 2 ^ n)
    {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : IsModO2Surj L α)
    (hq : IsLnTwoQuot L 3) (hZ : IsSumOfNaturalModulesVia L Z ⊥ α false k)
    (hyZ : y ∈ Subgroup.normalizer (Z : Set G)) (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyc : ∀ x ∈ L, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 L) (hodd : Odd (orderOf y)) (hAZ : A ≤ Z) :
    (∀ a ∈ A, y * a * y⁻¹ = a) ∨ (∀ a ∈ A, y * a * y⁻¹ = a → a = 1) := by
  have hF : Fintype.card F = 2 := card_eq_two_of_modO2Surj hq hFc hα
  obtain ⟨hLZ, -, β, hβs, hβk, hβe⟩ := hZ
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  have key := kc_nat hF hk (fun a => ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    (act_surj hα.1) β hβs hβi hLZ
    (fun a u v huv i => by simpa [moduleAct] using hβe a u v huv i) hyZ
    (exists_trivial_comm hα hyL hyc) hodd
  rcases key with h | h
  · exact Or.inl (fun a ha => h a (hAZ ha))
  · exact Or.inr (fun a ha => h a (hAZ ha))

theorem kc_of_module5 {L Q C A : Subgroup G} {y : G}
    {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))} (hα : IsModO2Surj L α)
    (hC2 : Nat.card C = 2) (hZ : IsSumOfNaturalModulesVia L Q C α false 1)
    (hyQ : y ∈ Subgroup.normalizer (Q : Set G)) (hyC : y ∈ Subgroup.normalizer (C : Set G))
    (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyc : ∀ x ∈ L, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 L) (hodd : Odd (orderOf y)) (hAQ : A ≤ Q)
    (hAc : ∀ a ∈ A, ∀ q ∈ Q, a * q = q * a) : ∀ a ∈ A, y * a * y⁻¹ = a := by
  obtain ⟨hLQ, -, β, hβs, hβk, hβe⟩ := hZ
  exact kc_case5 (F := ZMod 2) (by simp) (fun a => ((α a : GL (Fin 3) (ZMod 2)) :
    Matrix (Fin 3) (Fin 3) (ZMod 2))) (act_surj hα.1) β hβs hβk hLQ
    (fun a u v huv i => by simpa [moduleAct] using hβe a u v huv i) hyQ hyC
    (exists_trivial_comm hα hyL hyc) hC2 hodd hAQ hAc

end Packaged

end SBd5

end CFSG.Quasithin
