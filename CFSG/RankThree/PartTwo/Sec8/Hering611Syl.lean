module

public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.PartTwo.Sec6.Item611Res7ProofL2Facts
import CFSG.RankThree.PartTwo.KFacts.K71Lift
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_sylow {L : Subgroup G}
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * 2)))
    {X : Subgroup G} (hXL : X ≤ L) (hX3 : IsPGroup 3 X) :
    ∃ S₀ : Subgroup G, X ≤ S₀ ∧ S₀ ≤ L ∧ CFSG.Assembly.IsElemAbelian 3 S₀ ∧
      Nat.card S₀ = 3 ^ 6 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θL := aschbacherSolvableCore 3 L with hθL
  set F := GaloisField 3 (3 * 2) with hF
  set ψ : L ⧸ θL ≃* CFSG.GorensteinWalter.PSL2 F := φ.trans (Sec4.projSLEquivPSL F) with hψ
  have hFcard : Nat.card F = 3 ^ (3 * 2) := GaloisField.card 3 (3 * 2) (by omega)
  have hm1 : (-1 : F) ≠ 1 := by
    intro h
    have h2 : (2 : F) = 0 := by linear_combination -h
    have : ((2 : ℕ) : F) = 0 := by exact_mod_cast h2
    rw [CharP.cast_eq_zero_iff F 3] at this
    omega
  have hPSL : Nat.card (CFSG.GorensteinWalter.PSL2 F) = 193709880 := by
    have h := Sec6.Res611Res7.card_psl2_mul_two hm1
    rw [hFcard] at h
    norm_num at h
    omega
  have hLb : Nat.card (L ⧸ θL) = 193709880 := by rw [Nat.card_congr ψ.toEquiv, hPSL]
  have hθ3 : ¬ 3 ∣ Nat.card θL := KFacts.not_three_dvd_card_aschbacherSolvableCore L
  set Y : Subgroup L := X.subgroupOf L with hY
  have hY3 : IsPGroup 3 Y := hX3.comap_of_injective L.subtype L.subtype_injective
  obtain ⟨P, hYP⟩ := hY3.exists_le_sylow
  have hPcard : Nat.card P = 3 ^ 6 := by
    rw [Sylow.card_eq_multiplicity]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup θL
    rw [hLb] at h1
    have hθ0 : Nat.card θL ≠ 0 := Nat.card_pos.ne'
    rw [h1, Nat.factorization_mul (by norm_num) hθ0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hθ3, add_zero,
      show (193709880 : ℕ) = 3 ^ 6 * 265720 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  set q : L →* L ⧸ θL := QuotientGroup.mk' θL with hq
  have hqP : ∀ p₁ ∈ (P : Subgroup L), ∀ p₂ ∈ (P : Subgroup L), q p₁ = q p₂ → p₁ = p₂ := by
    intro p₁ h₁ p₂ h₂ h12
    have hker : p₁⁻¹ * p₂ ∈ θL := (QuotientGroup.eq).mp h12
    have hmem : p₁⁻¹ * p₂ ∈ (P : Subgroup L) := (P : Subgroup L).mul_mem
      ((P : Subgroup L).inv_mem h₁) h₂
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨p₁⁻¹ * p₂, hmem⟩
    have hk' : (p₁⁻¹ * p₂) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact inv_mul_eq_one.mp (KFacts.eq_one_of_mem_aschbacherSolvableCore_of_pow hker hk')
  set g : (P : Subgroup L) →* CFSG.GorensteinWalter.PSL2 F :=
    ψ.toMonoidHom.comp (q.comp (P : Subgroup L).subtype) with hg
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : q (x : L) = 1 := by
      have : ψ (q (x : L)) = 1 := hx
      exact ψ.injective (by rw [this, map_one])
    have h2 : q (x : L) = q 1 := by rw [h1, map_one]
    exact Subtype.ext (hqP _ x.2 1 (P : Subgroup L).one_mem h2)
  set Q : Subgroup (CFSG.GorensteinWalter.PSL2 F) := g.range with hQ
  have hQcard : Nat.card Q = 3 ^ 6 := by
    rw [hQ, ← Nat.card_congr (MonoidHom.ofInjective hginj).toEquiv, hPcard]
  have hfact : (193709880 : ℕ).factorization 3 = 6 := by
    rw [show (193709880 : ℕ) = 3 ^ 6 * 265720 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  set Qs : Sylow 3 (CFSG.GorensteinWalter.PSL2 F) :=
    Sylow.ofCard Q (by rw [hPSL, hfact, hQcard]) with hQs
  obtain ⟨eQ⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hFcard Qs
  have hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
    intro x hx y hy
    have h1 := congrArg eQ (mul_comm (eQ.symm ⟨x, hx⟩) (eQ.symm ⟨y, hy⟩))
    rw [map_mul, map_mul, eQ.apply_symm_apply, eQ.apply_symm_apply] at h1
    exact congrArg Subtype.val h1
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have hmul3 : ∀ z : Multiplicative F, z ^ 3 = 1 := fun z => by
    rw [← ofAdd_toAdd z, ← ofAdd_nsmul, nsmul_eq_mul, Nat.cast_ofNat, h3, zero_mul, ofAdd_zero]
  have hQ3 : ∀ x ∈ Q, x ^ 3 = 1 := by
    intro x hx
    have h1 : (⟨x, hx⟩ : (Qs : Subgroup (CFSG.GorensteinWalter.PSL2 F))) ^ 3 = 1 := by
      calc (⟨x, hx⟩ : (Qs : Subgroup (CFSG.GorensteinWalter.PSL2 F))) ^ 3
          = eQ ((eQ.symm ⟨x, hx⟩) ^ 3) := by rw [map_pow, eQ.apply_symm_apply]
        _ = 1 := by rw [hmul3, map_one]
    simpa using congrArg Subtype.val h1
  have hPcomm : ∀ x y : (P : Subgroup L), x * y = y * x := by
    intro x y
    apply hginj
    rw [map_mul, map_mul]
    exact hQcomm _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  have hP3 : ∀ x : (P : Subgroup L), x ^ 3 = 1 := by
    intro x
    apply hginj
    rw [map_pow, map_one]
    exact hQ3 _ ⟨x, rfl⟩
  refine ⟨(P : Subgroup L).map L.subtype, ?_, Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hXL hx⟩, hYP (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨a', ha', ha'a⟩ := a.2
      obtain ⟨b', hb', hb'b⟩ := b.2
      apply Subtype.ext
      change (a : G) * (b : G) = (b : G) * (a : G)
      rw [← ha'a, ← hb'b]
      have := congrArg (fun z : (P : Subgroup L) => ((z : L) : G)) (hPcomm ⟨a', ha'⟩ ⟨b', hb'⟩)
      simpa using this
    · obtain ⟨a', ha', rfl⟩ := ha
      have := congrArg (fun z : (P : Subgroup L) => ((z : L) : G)) (hP3 ⟨a', ha'⟩)
      simpa using this
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hPcard]

end CFSG.RankThree.PartTwo.Sec8.Hering611
