module

public import CFSG.Sporadic.Co2Smith.HPModel

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open CFSG.Certificates.ExtraspecialNF
open scoped Matrix

universe u

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem sElt_zero : sElt 0 = 1 := by
  simp only [sElt, Nat.zero_mod, Nat.zero_div, tElt_zero, mul_one]

theorem pLift_zero : pLift 0 = 1 := by
  simp only [pLift, Nat.zero_mod, Nat.zero_div, tLift_zero, mul_one]

noncomputable abbrev mkHP :
    FibP →* Hprime := QuotientGroup.mk' _

@[expose] noncomputable def fibE :
    cfgCz.E →* FibP where
  toFun e := ⟨((e : Cz), 1), by rw [SmithConfig.mem_fibSub, map_one]; exact cfgCz.rho_E e⟩
  map_one' := rfl
  map_mul' _ _ := Subtype.ext (Prod.ext rfl (one_mul 1).symm)

@[expose] noncomputable def iotaE :
    cfgCz.E →* Hprime := mkHP.comp fibE

theorem iotaE_injective :
    Function.Injective iotaE := by
  rw [injective_iff_map_eq_one]
  intro e he
  have h := (QuotientGroup.eq_one_iff _).mp he
  rcases mem_normalClosure_zPair.mp h with h | h
  · exact Subtype.ext (congrArg (fun u : FibP => u.1.1) h)
  · exact absurd (congrArg (fun u : FibP => u.1.2) h).symm coverZ_ne_one

theorem card_E_cfgCz :
    Nat.card cfgCz.E = 512 := by
  show Nat.card (CFSG.pCore 2 Cz) = 512
  rw [natCard_pCore_Cz]
  norm_num

theorem iotaE_range_normal :
    iotaE.range.Normal := by
  refine ⟨fun y hy g => ?_⟩
  obtain ⟨e, rfl⟩ := hy
  obtain ⟨⟨⟨h, p⟩, hp⟩, rfl⟩ := QuotientGroup.mk_surjective g
  have hE : (CFSG.pCore 2 Cz).Normal := CFSG.pCore_normal
  refine ⟨⟨h * (e : Cz) * h⁻¹, hE.conj_mem _ e.2 h⟩, ?_⟩
  show mkHP (fibE _) = mkHP ⟨(h, p), hp⟩ * mkHP (fibE e) * (mkHP ⟨(h, p), hp⟩)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  refine Subtype.ext (Prod.ext rfl ?_)
  show (1 : PGcov) = p * 1 * p⁻¹
  group

theorem fpElt_zero
    (e : ℕ) :
    fpElt e 0 = fibE ⟨⟨qElt e, Qsub_le_Cz (qElt_mem e)⟩, by
      show _ ∈ CFSG.pCore 2 Cz
      rw [pCore_Cz]
      exact qElt_mem e⟩ := by
  apply Subtype.ext
  refine Prod.ext (Subtype.ext ?_) pLift_zero
  show cElt e 0 = qElt e
  rw [cElt, sElt_zero, one_mul]

theorem mem_range_iotaE
    {y : Hprime} : y ∈ iotaE.range ↔ ∃ e < 512, hpElt e 0 = y := by
  constructor
  · rintro ⟨⟨q, hq⟩, rfl⟩
    have hq' : (q : K) ∈ Qsub := by
      have : q ∈ CFSG.pCore 2 Cz := hq
      rw [pCore_Cz] at this
      exact this
    obtain ⟨e, he, hqe⟩ := exists_qElt hq'
    refine ⟨e, he, ?_⟩
    rw [hpElt, fpElt_zero e]
    congr 2
    exact Subtype.ext (Subtype.ext hqe)
  · rintro ⟨e, -, rfl⟩
    rw [hpElt, fpElt_zero e]
    exact ⟨_, rfl⟩

theorem mem_pCore_Hprime
    {H : Type u} [Group H] [Finite H] (hH : SmithLocal H)
    (φ : H ≃* Hprime) {y : Hprime} :
    y ∈ CFSG.pCore 2 Hprime ↔ ∃ e < 512, hpElt e 0 = y := by
  rw [← mem_range_iotaE]
  have hcard : Nat.card iotaE.range = 512 := by
    rw [← card_E_cfgCz]
    exact Nat.card_congr (MonoidHom.ofInjective iotaE_injective).toEquiv.symm
  have hp : IsPGroup 2 iotaE.range := IsPGroup.of_card (n := 9) (by rw [hcard]; norm_num)
  have hle : iotaE.range ≤ CFSG.pCore 2 Hprime := by
    have := iotaE_range_normal
    unfold CFSG.pCore
    exact le_sSup ⟨this, hp⟩
  have hcp : Nat.card (CFSG.pCore 2 Hprime) = 512 := by
    rw [← map_pCore_two φ, Subgroup.card_map_of_injective φ.injective, hH.card_pCore]
    norm_num
  have heq : iotaE.range = CFSG.pCore 2 Hprime :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcp, hcard])
  rw [heq]

@[expose] noncomputable def piHP :
    Hprime →* S0 :=
  QuotientGroup.lift _ (covMap.comp ((MonoidHom.snd _ _).comp FibP.subtype)) (by
    refine Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr ?_)
    show covMap coverZ = 1
    exact covMap_coverZ)

theorem piHP_hpElt
    (e n : ℕ) : (piHP (hpElt e n) : K) = sElt n := by
  show (covMap (pLift n) : K) = sElt n
  exact covMap_pLift n

theorem rho_S0
    {s : K} (hs : s ∈ S0) : cfgCz.rho ⟨s, S0_le_Cz hs⟩ = ⟨s, hs⟩ :=
  cfgCz.rho_ι ⟨s, hs⟩

end CFSG.Sporadic.Co2Smith
