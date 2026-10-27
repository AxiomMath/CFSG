module

public import CFSG.Quasithin.H13.NQBlockRadicalFactorization
public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.GroupAction.Quotient
public import CFSG.Quasithin.H13.NQBlockPrimeResidualCenter
public import CFSG.Quasithin.H13.NQBlockSourceRank
public import CFSG.Quasithin.H13.NQBlockThompsonTransport
public import CFSG.Quasithin.H13.NQTermThompsonFactorization
public import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem witness_sylow_product {T L M : Subgroup G} (h : QTNQ T L M) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {X : Subgroup G} (hXN : X ≤ (CFSG.solvableRadical ↥L).map L.subtype)
    (hXc : (X.subgroupOf L).Characteristic) (hXA : IsPGroup p (↥X ⧸ CFSG.pCore 2 ↥X))
    {P : Subgroup G} (hPT : P ≤ T) (hMP : pCoreOf 2 M ≤ P) :
    X ⊔ P ≤ M ∧ X ⊓ P = pCoreOf 2 X ∧ Group.IsSolvable ↥(X ⊔ P) ∧
      ¬ 3 ∣ Nat.card ↥(X ⊔ P) ∧ QuasithinUnique.IsSylowTwoOf P (X ⊔ P) ∧
      pCoreOf 2 M ≤ pCoreOf 2 (X ⊔ P) ∧ QuasithinUnique.CharTwo (X ⊔ P) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  set N := (CFSG.solvableRadical ↥L).map L.subtype with hNdef
  have hNL : N ≤ L := map_subtype_le _
  have hXL : X ≤ L := hXN.trans hNL
  have hLM : L ≤ M := h.l_le
  have hTM : T ≤ M := h.t_le
  have hP2 : IsPGroup 2 P := h.sylow.1.to_le hPT
  have hMX : M ≤ normalizer (X : Set G) := by
    have hXeq : (X.subgroupOf L).map L.subtype = X := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXL]
    have := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := L) (X.subgroupOf L)
    rw [hXeq] at this
    exact h.eq_normalizer.le.trans this
  have hPX : P ≤ normalizer (X : Set G) := (hPT.trans hTM).trans hMX
  have hVM : X ⊔ P ≤ M := sup_le (hXL.trans hLM) (hPT.trans hTM)
  have hQXM : pCoreOf 2 X ≤ pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans (hXL.trans hLM))
      (hMX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  have hMn : M ≤ normalizer (pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hXP : X ⊓ P = pCoreOf 2 X := by
    refine le_antisymm (fun x hx => ?_) (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
      (hQXM.trans hMP))
    obtain ⟨hxX, hxP⟩ := mem_inf.mp hx
    rw [← mem_pCore_iff_mem_pCoreOf (b := ⟨x, hxX⟩), ← QuotientGroup.eq_one_iff]
    set xb : ↥X ⧸ CFSG.pCore 2 ↥X := QuotientGroup.mk (⟨x, hxX⟩ : ↥X) with hxb
    obtain ⟨k, hk⟩ := hXA xb
    obtain ⟨m, hm⟩ := hP2 ⟨x, hxP⟩
    have hm' : xb ^ 2 ^ m = 1 := by
      have h1 : x ^ 2 ^ m = 1 := by
        have := congrArg Subtype.val hm
        rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
      rw [hxb, ← QuotientGroup.mk_pow]
      have h2 : (⟨x, hxX⟩ : ↥X) ^ 2 ^ m = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact h1)
      rw [h2, QuotientGroup.mk_one]
    have hcop : Nat.Coprime (p ^ k) (2 ^ m) := by
      apply Nat.Coprime.pow
      rw [Nat.coprime_primes hp Nat.prime_two]
      omega
    have h1 : orderOf xb ∣ Nat.gcd (p ^ k) (2 ^ m) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one hm')
    rw [Nat.Coprime.gcd_eq_one hcop] at h1
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  have hXs : Group.IsSolvable ↥X := by
    obtain ⟨-, hNs, -, -⟩ := CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization ↥L
    have hNs' : Group.IsSolvable ↥N := by
      have := hNs
      exact Group.isSolvable_of_surjective (f := ((CFSG.solvableRadical ↥L).equivMapOfInjective
        L.subtype L.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
    have : Group.IsSolvable ↥(X.subgroupOf N) := subgroup_solvable_of_solvable _
    exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hXN).toMonoidHom)
      (MulEquiv.surjective _)
  have hPs : Group.IsSolvable ↥P := by
    have : Group.IsNilpotent ↥P := hP2.isNilpotent
    infer_instance
  have hVs : Group.IsSolvable ↥(X ⊔ P) :=
    CFSG.RankThree.GroupTheory.isSolvable_sup_of_le_normalizer hPX hXs hPs
  have hcardQ : Nat.card ↥(pCoreOf 2 X) = Nat.card ↥(CFSG.pCore 2 ↥X) := by
    exact Subgroup.card_map_of_injective X.subtype_injective
  have hcardX := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥X)
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hPX
  rw [hXP, hcardQ, hcardX] at hprod
  have hpos : 0 < Nat.card ↥(CFSG.pCore 2 ↥X) := Nat.card_pos
  have hcardV : Nat.card ↥(X ⊔ P) = Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) * Nat.card P := by
    have h1 : Nat.card ↥(X ⊔ P) * Nat.card ↥(CFSG.pCore 2 ↥X) =
        (Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) * Nat.card P) * Nat.card ↥(CFSG.pCore 2 ↥X) := by
      rw [hprod]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  obtain ⟨b, hb⟩ := hXA.exists_card_eq
  obtain ⟨c, hc⟩ := hP2.exists_card_eq
  have h3 : ¬ 3 ∣ Nat.card ↥(X ⊔ P) := by
    rw [hcardV, hb, hc]
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h3 | h3
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
  have hidx : P.relIndex (X ⊔ P) = Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) := by
    have h1 := Subgroup.relIndex_mul_card P (X ⊔ P)
    rw [inf_eq_left.mpr le_sup_right, hcardV] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hSyl : QuasithinUnique.IsSylowTwoOf P (X ⊔ P) := by
    refine ⟨le_sup_right, hP2, ?_⟩
    change ¬ 2 ∣ P.relIndex (X ⊔ P)
    rw [hidx, hb]
    intro h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h2)
    omega
  have hMV : pCoreOf 2 M ≤ pCoreOf 2 (X ⊔ P) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hMP.trans le_sup_right)
      (hVM.trans hMn) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  have hT' : QuasithinUnique.IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, h.sylow.1, ?_⟩
    change ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact h.sylow.2
  have hMc : QuasithinUnique.CharTwo M :=
    QuasithinUnique.charTwo_of_isTwoLocal_of_isSylowTwoOf_le h.qtke.2.1 hT'
      h.max_two_local.1 hTM
  have hVc : QuasithinUnique.CharTwo (X ⊔ P) := fun x hx =>
    hMV (hMc ⟨hVM hx.1, centralizer_le hMV hx.2⟩)
  exact ⟨hVM, hXP, hVs, h3, hSyl, hMV, hVc⟩

theorem sylow_thompson_factorization {V P : Subgroup G} (hVs : Group.IsSolvable ↥V)
    (h3 : ¬ 3 ∣ Nat.card ↥V) (hVc : QuasithinUnique.CharTwo V)
    (hSyl : QuasithinUnique.IsSylowTwoOf P V) :
    (V : Set G) =
      ((V ⊓ normalizer ((CFSG.elemThompson ↥P 2).map P.subtype : Set G) : Subgroup G) : Set G) *
        ((V ⊓ centralizer (omegaOneCenterOf 2 P : Set G) : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsSolvable ↥V := hVs
  have hPV : P ≤ V := hSyl.1
  have hchar : CFSG.IsCharacteristicP 2 ↥V :=
    QuasithinUnique.EscapingLocal.isCharacteristicP_of_charTwo hVc
  have hF : CFSG.generalizedFitting ↥V = CFSG.pCore 2 ↥V :=
    (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥V 2).mp hchar
  have hP2V : IsPGroup 2 ↥(P.subgroupOf V) :=
    hSyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPV).symm
  set S : Sylow 2 ↥V := hP2V.toSylow hSyl.2.2 with hSdef
  have hScoe : (S : Subgroup ↥V) = P.subgroupOf V := IsPGroup.toSylow_coe hP2V hSyl.2.2
  obtain ⟨-, -, -, -, -, -, f3, -⟩ :=
    NQTerm.solvable_characteristic_two_three_free_thompson_factorization hF h3 S rfl rfl rfl
  have hZmap : (quasithinOmegaOneCenter (S : Subgroup ↥V)).map V.subtype =
      omegaOneCenterOf 2 P := by
    rw [hScoe]
    exact map_quasithinOmegaOneCenter_subgroupOf hPV
  set e' : ↥(S : Subgroup ↥V) ≃* ↥P :=
    (MulEquiv.subgroupCongr hScoe).trans (Subgroup.subgroupOfEquivOfLe hPV) with he'def
  have hJmap : ((CFSG.elemThompson ↥(S : Subgroup ↥V) 2).map (S : Subgroup ↥V).subtype).map
      V.subtype = (CFSG.elemThompson ↥P 2).map P.subtype := by
    rw [← CFSG.higherElemThompson_zero, ← CFSG.higherElemThompson_zero,
      ← map_higherElemThompson e' 0, Subgroup.map_map, Subgroup.map_map]
    rfl
  refine coe_eq_mul_of_mul_eq_univ f3 (fun a ha => ?_) (fun b hb => ?_)
  · rw [← hJmap]
    exact coe_mem_normalizer_map ha
  · rw [← hZmap]
    exact coe_mem_centralizer_map hb

end CFSG.Quasithin.H13.NQBlock
