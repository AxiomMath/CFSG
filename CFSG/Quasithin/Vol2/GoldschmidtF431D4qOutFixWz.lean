module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutFixSyl
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutFixTrace
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Cent

public section

namespace CFSG.Quasithin.H13.F431.D4q.Out

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.D4q.Struct CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

set_option linter.unusedSectionVars false


section Probes

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ δ : K ≃+* K}
  (hσ3 : σ.toRingHom ^ 3 = 1)

include hσ3 in
theorem exists_Ug_coord {a b c d e f : K} (hb : σ b = b) (he : σ e = e) (hf : σ f = f)
    (h : δ a = a ∧ δ b = b ∧ δ c = c ∧ δ d = d ∧ δ e = e ∧ δ f = f) :
    ∃ v : Cm σ, v ∈ Ug σ δ ∧ (v : ModGL TwistTag.D4.tag K) = d4x₁ K σ a * d4v K σ b c d e f :=
  ⟨coordElt hσ3 (a := a) (c := c) (d := d) hb he hf,
    ⟨coordElt_mem_Ust hσ3 hb he hf,
      (fieldActor_fix_iff σ δ _ (coe_coordElt hσ3 hb he hf)).2 h⟩, coe_coordElt hσ3 hb he hf⟩

include hσ3 in
theorem exists_Ug_x₃ {c : K} (hc : δ c = c) :
    ∃ v : Cm σ, v ∈ Ug σ δ ∧ (v : ModGL TwistTag.D4.tag K) = d4x₃ K σ c := by
  obtain ⟨v, hv, hv'⟩ := exists_Ug_coord hσ3 (δ := δ) (a := 0) (b := 0) (c := c) (d := 0) (e := 0)
    (f := 0) (map_zero σ) (map_zero σ) (map_zero σ)
    ⟨map_zero δ, map_zero δ, hc, map_zero δ, map_zero δ, map_zero δ⟩
  exact ⟨v, hv, by rw [hv', d4x₁_zero, one_mul, d4x₃_eq_d4v σ]⟩

include hσ3 in
theorem exists_Ug_x₄ {d : K} (hd : δ d = d) :
    ∃ v : Cm σ, v ∈ Ug σ δ ∧ (v : ModGL TwistTag.D4.tag K) = d4x₄ K σ d := by
  obtain ⟨v, hv, hv'⟩ := exists_Ug_coord hσ3 (δ := δ) (a := 0) (b := 0) (c := 0) (d := d) (e := 0)
    (f := 0) (map_zero σ) (map_zero σ) (map_zero σ)
    ⟨map_zero δ, map_zero δ, map_zero δ, hd, map_zero δ, map_zero δ⟩
  exact ⟨v, hv, by rw [hv', d4x₁_zero, one_mul, d4x₄_eq_d4v σ]⟩

include hσ3 in
theorem exists_Ug_x₆_one :
    ∃ v : Cm σ, v ∈ Ug σ δ ∧ (v : ModGL TwistTag.D4.tag K) = d4x₆ K 1 := by
  obtain ⟨v, hv, hv'⟩ := exists_Ug_coord hσ3 (δ := δ) (a := 0) (b := 0) (c := 0) (d := 0) (e := 0)
    (f := 1) (map_zero σ) (map_zero σ) (map_one σ)
    ⟨map_zero δ, map_zero δ, map_zero δ, map_zero δ, map_zero δ, map_one δ⟩
  exact ⟨v, hv, by rw [hv', d4x₁_zero, one_mul, d4x₆_eq_d4v σ]⟩

end Probes

section Wz

variable {K : Type} [Field K] [Finite K] (σ δ : K ≃+* K) {f e : ℕ} (hf : 1 ≤ f) (hfe : f = 2 * e)
  (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ.toRingHom c = c ^ (2 ^ f))
  (hδ : ∀ c, δ c = c ^ 2 ^ (3 * e))

include hf hfe hK hσ hδ in
theorem conj_z_mem_Wg {S2 : Subgroup (K ≃+* K)} {T : Subgroup (MulAut (Cm σ))}
    (hT : ∀ α : MulAut (Cm σ), α ∈ T ↔ ∃ u ∈ Ust σ, ∃ δ' ∈ S2, α = MulAut.conj u *
      fieldActor σ δ') (z : Cm σ) (hz : (z : ModGL TwistTag.D4.tag K) = d4z K) :
    MulAut.conj z ∈ centerOf (Tg σ δ T) ⊓ ⁅Tg σ δ T, Tg σ δ T⁆ := by
  subst hfe
  have he : 1 ≤ e := by omega
  have hK6 : Nat.card K = 2 ^ (6 * e) := by
    rw [hK, ← pow_mul]
    ring_nf
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK6
  have hσ3' : ∀ c, σ (σ (σ c)) = c := CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card
    (σ := σ.toRingHom) hK hσ
  have hσ3 : σ.toRingHom ^ 3 = 1 := toRingHom_pow_three_d4 σ hσ3'
  obtain ⟨z', hz'Ug, hz'⟩ := exists_Ug_x₆_one hσ3 (δ := δ)
  have hzz : z = z' := Subtype.ext (by rw [hz, hz']; rfl)
  subst hzz
  have hzc : (z : ModGL TwistTag.D4.tag K) = d4x₁ K σ 0 * d4v K σ 0 0 0 0 1 := by
    rw [hz', d4x₆_eq_d4v σ, d4x₁_zero, one_mul]
  have hfixall : ∀ δ' : K ≃+* K, fieldActor σ δ' z = z := fun δ' =>
    (fieldActor_fix_iff σ δ' z hzc).2 ⟨map_zero δ', map_zero δ', map_zero δ', map_zero δ',
      map_zero δ', map_one δ'⟩
  have hzTg : MulAut.conj z ∈ Tg σ δ T :=
    (mem_Tg_iff σ δ hT _).2 ⟨z, hz'Ug, 1, S2.one_mem, by rw [fieldActor_one, mul_one]⟩
  refine ⟨⟨hzTg, Subgroup.mem_centralizer_iff.2 fun α hα => ?_⟩, ?_⟩
  · obtain ⟨u, hu, δ', hδ', rfl⟩ := (mem_Tg_iff σ δ hT α).1 hα
    have h1 : (u : Cm σ) * z = z * u := by
      refine Subtype.ext ?_
      have hu' : (u : ModGL TwistTag.D4.tag K) ∈
          graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := Subgroup.mem_subgroupOf.1 hu.1
      have := commute_d4x₆_of_mem σ hσ3' hu' 1
      show (u : ModGL TwistTag.D4.tag K) * (z : ModGL TwistTag.D4.tag K) =
        (z : ModGL TwistTag.D4.tag K) * (u : ModGL TwistTag.D4.tag K)
      rw [hz']
      exact this
    have h2 : (fieldActor σ δ' : MulAut (Cm σ)) * MulAut.conj z = MulAut.conj z *
        fieldActor σ δ' := by
      rw [mulAut_mul_conj σ, hfixall]
    calc (MulAut.conj u * fieldActor σ δ') * MulAut.conj z =
        MulAut.conj u * (fieldActor σ δ' * MulAut.conj z) := mul_assoc _ _ _
      _ = MulAut.conj u * (MulAut.conj z * fieldActor σ δ') := by rw [h2]
      _ = (MulAut.conj u * MulAut.conj z) * fieldActor σ δ' := (mul_assoc _ _ _).symm
      _ = (MulAut.conj z * MulAut.conj u) * fieldActor σ δ' := by
          rw [← map_mul, ← map_mul, h1]
      _ = MulAut.conj z * (MulAut.conj u * fieldActor σ δ') := mul_assoc _ _ _
  · obtain ⟨t, ht, hts⟩ := exists_trace_one he hK6 (fun c => hσ c) hδ
    obtain ⟨xa, hxaUg, hxa⟩ := exists_Ug_x₄ hσ3 (δ := δ) ht
    obtain ⟨xb, hxbUg, hxb⟩ := exists_Ug_x₃ hσ3 (δ := δ) (c := 1) (map_one δ)
    have hxaT : MulAut.conj xa ∈ Tg σ δ T :=
      (mem_Tg_iff σ δ hT _).2 ⟨xa, hxaUg, 1, S2.one_mem, by rw [fieldActor_one, mul_one]⟩
    have hxbT : MulAut.conj xb ∈ Tg σ δ T :=
      (mem_Tg_iff σ δ hT _).2 ⟨xb, hxbUg, 1, S2.one_mem, by rw [fieldActor_one, mul_one]⟩
    have hcomm : ⁅xa, xb⁆ = z := by
      refine Subtype.ext ?_
      have h1 : ((⁅xa, xb⁆ : Cm σ) : ModGL TwistTag.D4.tag K) =
          ⁅(xa : ModGL TwistTag.D4.tag K), (xb : ModGL TwistTag.D4.tag K)⁆ := rfl
      rw [h1, hxa, hxb, comm_d4x₄_d4x₃ σ hσ3' t 1, mul_one, hts, hz']
    have := Subgroup.commutator_mem_commutator hxaT hxbT
    rwa [← map_commutatorElement, hcomm] at this

end Wz


end CFSG.Quasithin.H13.F431.D4q.Out
