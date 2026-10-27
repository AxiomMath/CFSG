module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.Quasithin.A312Ru

open CFSG.Quasithin
open scoped commutatorElement

variable {Y H : Type} [Group Y] [Finite Y] [Group H] [Finite H]

theorem perfectCore_top_normal (Y : Type) [Group Y] : (perfectCore (⊤ : Subgroup Y)).Normal := by
  refine Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr ?_)
  exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)

theorem commutator_eq_top_of_simple {S : Type} [Group S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) : commutator S = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hS
    apply hab
    have hmem : ⁅a, b⁆ ∈ commutator S :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  · exact h

theorem map_perfectCore_eq (ρ : Y →* H) (hρ : Function.Surjective ρ) (A : Subgroup H) [A.Normal]
    [IsSimpleGroup A] (hAnab : ∃ a b : A, a * b ≠ b * a) (hHA : IsPGroup 2 (H ⧸ A)) :
    (perfectCore (⊤ : Subgroup Y)).map ρ = A := by
  rw [map_perfectCore, Subgroup.map_top_of_surjective ρ hρ]
  apply le_antisymm
  · have hq := map_perfectCore (QuotientGroup.mk' A) (⊤ : Subgroup H)
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective A)] at hq
    have : Group.IsNilpotent (H ⧸ A) := hHA.isNilpotent
    have hsolv : Group.IsSolvable (↥(⊤ : Subgroup (H ⧸ A))) := inferInstance
    have hbot := (isSolvable_iff_perfectCore_eq_bot _).mp hsolv
    rw [hbot] at hq
    have := (Subgroup.map_eq_bot_iff _).mp hq
    rwa [QuotientGroup.ker_mk'] at this
  · have hperf : ⁅A, A⁆ = A := by
      have : Group.IsPerfect A := Group.isPerfect_def.mpr (commutator_eq_top_of_simple hAnab)
      exact Subgroup.isPerfect_iff.mp this
    exact le_perfectCore_of_perfect le_top hperf

theorem perfectCore_quot (ρ : Y →* H) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = CFSG.pCore 2 Y) (A : Subgroup H) [A.Normal] [IsSimpleGroup A]
    (hAnab : ∃ a b : A, a * b ≠ b * a) (hHA : IsPGroup 2 (H ⧸ A))
    (hq : ∀ (N : Subgroup Y) [N.Normal], IsPGroup 2 (Y ⧸ N) →
      Nat.card (Y ⧸ N) ≤ Nat.card (H ⧸ A)) :
    ∃ f : ↥(perfectCore (⊤ : Subgroup Y)) →* A, Function.Surjective f ∧
      (∀ r, (f r : H) = ρ r) ∧ IsPGroup 2 f.ker ∧
      CFSG.pCore 2 Y ≤ perfectCore (⊤ : Subgroup Y) ∧
      Nat.card (CFSG.pCore 2 ↥(perfectCore (⊤ : Subgroup Y))) = Nat.card (CFSG.pCore 2 Y) ∧
      Nonempty (↥(perfectCore (⊤ : Subgroup Y)) ⧸ CFSG.pCore 2 ↥(perfectCore (⊤ : Subgroup Y)) ≃*
        A) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup Y := perfectCore (⊤ : Subgroup Y) with hR
  have hRn : R.Normal := perfectCore_top_normal Y
  set P : Subgroup Y := CFSG.pCore 2 Y with hPdef
  have hPn : P.Normal := CFSG.pCore_normal
  have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup
  have hmap : R.map ρ = A := map_perfectCore_eq ρ hρ A hAnab hHA
  have hmem : ∀ r : R, ρ r ∈ A := fun r => hmap ▸ Subgroup.mem_map_of_mem ρ r.2
  let f : ↥R →* A := (ρ.comp R.subtype).codRestrict A hmem
  have hfs : Function.Surjective f := by
    intro a
    have ha : (a : H) ∈ R.map ρ := hmap ▸ a.2
    obtain ⟨r, hr, hra⟩ := ha
    exact ⟨⟨r, hr⟩, Subtype.ext hra⟩
  have hKer : f.ker = P.subgroupOf R := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hker, MonoidHom.mem_ker]
    have hfr : ((f r : A) : H) = ρ (r : Y) := rfl
    constructor
    · intro h
      rw [← hfr, h]
      rfl
    · intro h
      apply Subtype.ext
      rw [hfr, h]
      rfl
  have hcardY : Nat.card Y = Nat.card H * Nat.card P := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    rwa [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).toEquiv, hker] at h1
  have hcardR : Nat.card R = Nat.card A * Nat.card f.ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rwa [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hfs).toEquiv] at h1
  have hcardH : Nat.card H = Nat.card (H ⧸ A) * Nat.card A :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup A
  have hcardYR : Nat.card Y = Nat.card (Y ⧸ R) * Nat.card R :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup R
  have hkey : Nat.card (Y ⧸ R) * Nat.card f.ker = Nat.card (H ⧸ A) * Nat.card P := by
    have hApos : 0 < Nat.card A := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_left hApos ?_
    calc Nat.card A * (Nat.card (Y ⧸ R) * Nat.card f.ker)
        = Nat.card (Y ⧸ R) * (Nat.card A * Nat.card f.ker) := by ring
      _ = Nat.card (Y ⧸ R) * Nat.card R := by rw [hcardR]
      _ = Nat.card Y := hcardYR.symm
      _ = Nat.card H * Nat.card P := hcardY
      _ = Nat.card A * (Nat.card (H ⧸ A) * Nat.card P) := by rw [hcardH]; ring
  obtain ⟨m, hm⟩ := hP2.exists_card_eq
  obtain ⟨k, hk⟩ := hHA.exists_card_eq
  have hdvd : Nat.card (Y ⧸ R) ∣ 2 ^ (k + m) :=
    ⟨Nat.card f.ker, by rw [pow_add, ← hk, ← hm, ← hkey]⟩
  obtain ⟨t, -, ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hRp : IsPGroup 2 (Y ⧸ R) := IsPGroup.of_card ht
  have hle := hq R hRp
  have hPle : Nat.card P ≤ Nat.card f.ker := by
    by_contra hlt
    push Not at hlt
    have hq0 : 0 < Nat.card (H ⧸ A) := Nat.card_pos
    have : Nat.card (Y ⧸ R) * Nat.card f.ker < Nat.card (H ⧸ A) * Nat.card P :=
      calc Nat.card (Y ⧸ R) * Nat.card f.ker ≤ Nat.card (H ⧸ A) * Nat.card f.ker :=
            Nat.mul_le_mul_right _ hle
        _ < Nat.card (H ⧸ A) * Nat.card P := Nat.mul_lt_mul_of_pos_left hlt hq0
    omega
  have hPR : P ≤ R := by
    let g : ↥(P.subgroupOf R) → P := fun r => ⟨((r : R) : Y), Subgroup.mem_subgroupOf.mp r.2⟩
    have hginj : Function.Injective g := by
      intro r1 r2 h
      have h1 : (g r1).1 = (g r2).1 := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h1)
    have hbij : Function.Bijective g :=
      hginj.bijective_of_nat_card_le (by rw [← hKer]; exact hPle)
    intro x hx
    obtain ⟨r, hr⟩ := hbij.2 ⟨x, hx⟩
    have : ((r : R) : Y) = x := congrArg Subtype.val hr
    rw [← this]
    exact (r : R).2
  have hP2R : IsPGroup 2 (P.subgroupOf R) := hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPR).symm
  have hOcore : CFSG.pCore 2 ↥R = f.ker := by
    apply le_antisymm
    · have hOn : (CFSG.pCore 2 ↥R).Normal := CFSG.pCore_normal
      have hO2 : IsPGroup 2 (CFSG.pCore 2 ↥R) := CFSG.pCore_isPGroup
      have hfO : ((CFSG.pCore 2 ↥R).map f).Normal := Subgroup.Normal.map hOn f hfs
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥R).map f) with h | h
      · exact (Subgroup.map_eq_bot_iff _).mp h
      · exfalso
        have h2 : IsPGroup 2 ((CFSG.pCore 2 ↥R).map f) := hO2.map f
        rw [h] at h2
        have hA2 : IsPGroup 2 A := h2.of_equiv Subgroup.topEquiv
        have hnil : Group.IsNilpotent A := hA2.isNilpotent
        have hperf : Group.IsPerfect A :=
          Group.isPerfect_def.mpr (commutator_eq_top_of_simple hAnab)
        exact Group.IsPerfect.not_isNilpotent (G := A) hnil
    · rw [hKer]
      exact le_sSup ⟨inferInstance, hP2R⟩
  have hPR' : Nat.card (P.subgroupOf R) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPR).toEquiv
  refine ⟨f, hfs, fun r => rfl, ?_, hPR, ?_, ?_⟩
  · rw [hKer]; exact hP2R
  · rw [hOcore, hKer, hPR']
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq hOcore).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfs)⟩

end CFSG.Quasithin.A312Ru
