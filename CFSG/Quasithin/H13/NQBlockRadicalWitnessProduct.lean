module

public import CFSG.Quasithin.H13.NQBlockSourceRank
public import CFSG.Quasithin.H13.NQCoreEscapingBasic
public import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual
public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.Adapters.QiuzhenLegacy.FeitThompson.GroupAction.Quotient

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem radical_witness_product {T L M : Subgroup G} (h : QTNQ T L M) {R : Subgroup G}
    (hR : (R : Set G) = nqOriginalCentralizer T L) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {X : Subgroup G} (hXN : X ≤ (CFSG.solvableRadical ↥L).map L.subtype)
    (hXc : (X.subgroupOf L).Characteristic) (hXA : IsPGroup p (↥X ⧸ CFSG.pCore 2 ↥X)) :
    M ≤ normalizer (X : Set G) ∧ X ⊔ R ≤ M ∧ IsPGroup 2 R ∧
      pCoreOf 2 X ≤ pCoreOf 2 M ∧ pCoreOf 2 M ≤ R ∧ X ⊓ R = pCoreOf 2 X ∧
      Group.IsSolvable ↥(X ⊔ R) ∧
      Nat.card ↥(X ⊔ R) = Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) * Nat.card R ∧
      ¬ 3 ∣ Nat.card ↥(X ⊔ R) ∧ QuasithinUnique.IsSylowTwoOf R (X ⊔ R) ∧
      pCoreOf 2 M ≤ pCoreOf 2 (X ⊔ R) ∧ QuasithinUnique.CharTwo (X ⊔ R) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  set N := (CFSG.solvableRadical ↥L).map L.subtype with hNdef
  have hNL : N ≤ L := map_subtype_le _
  have hXL : X ≤ L := hXN.trans hNL
  have hLM : L ≤ M := h.l_le
  have hTM : T ≤ M := h.t_le
  have hRT : R ≤ T := fun r hr => by
    rw [← SetLike.mem_coe, hR] at hr
    exact hr.1
  have hR2 : IsPGroup 2 R := h.sylow.1.to_le hRT
  have hMX : M ≤ normalizer (X : Set G) := by
    have hXeq : (X.subgroupOf L).map L.subtype = X := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXL]
    have := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := L) (X.subgroupOf L)
    rw [hXeq] at this
    exact h.eq_normalizer.le.trans this
  have hLnorm : M ≤ normalizer (L : Set G) := h.eq_normalizer.le
  have hRX : R ≤ normalizer (X : Set G) := (hRT.trans hTM).trans hMX
  have hVM : X ⊔ R ≤ M := sup_le (hXL.trans hLM) (hRT.trans hTM)
  have hQXM : pCoreOf 2 X ≤ pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans (hXL.trans hLM))
      (hMX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  have hMT : pCoreOf 2 M ≤ T :=
    QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf
      (NQCore.isSylowIn_of_quasithin h.sylow h.t_le)
  have hMn : M ≤ normalizer (pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hOL : pCoreOf 2 L ≤ N := by
    obtain ⟨-, -, hmax, -⟩ :=
      CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization ↥L
    have hle : CFSG.pCore 2 ↥L ≤ CFSG.solvableRadical ↥L := by
      refine hmax _ inferInstance ?_
      have : Group.IsNilpotent ↥(CFSG.pCore 2 ↥L) := (CFSG.pCore_isPGroup (p := 2)).isNilpotent
      infer_instance
    exact map_mono hle
  have hMR : pCoreOf 2 M ≤ R := by
    intro t ht
    rw [← SetLike.mem_coe, hR]
    refine ⟨hMT ht, fun l hl => hOL ?_⟩
    have htM : t ∈ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M ht
    have hc1 : t * l * t⁻¹ * l⁻¹ ∈ pCoreOf 2 M := by
      have e : t * l * t⁻¹ * l⁻¹ = t * (l * t⁻¹ * l⁻¹) := by group
      rw [e]
      exact mul_mem ht ((mem_normalizer_iff.mp (hMn (hLM hl)) _).mp (inv_mem ht))
    have hc2 : t * l * t⁻¹ * l⁻¹ ∈ L :=
      mul_mem ((mem_normalizer_iff.mp (hLnorm htM) l).mp hl) (inv_mem hl)
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun g hg => mem_normalizer_inf (hMn (hLM hg)) (le_normalizer hg))
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left) ⟨hc1, hc2⟩
  have hXR : X ⊓ R = pCoreOf 2 X := by
    refine le_antisymm (fun x hx => ?_) (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
      (hQXM.trans hMR))
    obtain ⟨hxX, hxR⟩ := mem_inf.mp hx
    rw [← mem_pCore_iff_mem_pCoreOf (b := ⟨x, hxX⟩), ← QuotientGroup.eq_one_iff]
    set xb : ↥X ⧸ CFSG.pCore 2 ↥X := QuotientGroup.mk (⟨x, hxX⟩ : ↥X) with hxb
    obtain ⟨k, hk⟩ := hXA xb
    obtain ⟨m, hm⟩ := hR2 ⟨x, hxR⟩
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
  have hRs : Group.IsSolvable ↥R := by
    have : Group.IsNilpotent ↥R := hR2.isNilpotent
    infer_instance
  have hVs : Group.IsSolvable ↥(X ⊔ R) :=
    CFSG.RankThree.GroupTheory.isSolvable_sup_of_le_normalizer hRX hXs hRs
  have hcardQ : Nat.card ↥(pCoreOf 2 X) = Nat.card ↥(CFSG.pCore 2 ↥X) := by
    exact Subgroup.card_map_of_injective X.subtype_injective
  have hcardX := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥X)
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hRX
  rw [hXR, hcardQ, hcardX] at hprod
  have hpos : 0 < Nat.card ↥(CFSG.pCore 2 ↥X) := Nat.card_pos
  have hcardV : Nat.card ↥(X ⊔ R) = Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) * Nat.card R := by
    have h1 : Nat.card ↥(X ⊔ R) * Nat.card ↥(CFSG.pCore 2 ↥X) =
        (Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) * Nat.card R) * Nat.card ↥(CFSG.pCore 2 ↥X) := by
      rw [hprod]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  obtain ⟨b, hb⟩ := hXA.exists_card_eq
  obtain ⟨c, hc⟩ := hR2.exists_card_eq
  have h3 : ¬ 3 ∣ Nat.card ↥(X ⊔ R) := by
    rw [hcardV, hb, hc]
    intro h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h3 | h3
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
  have hidx : R.relIndex (X ⊔ R) = Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) := by
    have h1 := Subgroup.relIndex_mul_card R (X ⊔ R)
    rw [inf_eq_left.mpr le_sup_right, hcardV] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hSyl : QuasithinUnique.IsSylowTwoOf R (X ⊔ R) := by
    refine ⟨le_sup_right, hR2, ?_⟩
    change ¬ 2 ∣ R.relIndex (X ⊔ R)
    rw [hidx, hb]
    intro h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h2)
    omega
  have hMV : pCoreOf 2 M ≤ pCoreOf 2 (X ⊔ R) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hMR.trans le_sup_right)
      (hVM.trans hMn) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  have hT' : QuasithinUnique.IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, h.sylow.1, ?_⟩
    change ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact h.sylow.2
  have hMc : QuasithinUnique.CharTwo M :=
    QuasithinUnique.charTwo_of_isTwoLocal_of_isSylowTwoOf_le h.qtke.2.1 hT'
      h.max_two_local.1 hTM
  have hVc : QuasithinUnique.CharTwo (X ⊔ R) := fun x hx =>
    hMV (hMc ⟨hVM hx.1, centralizer_le hMV hx.2⟩)
  exact ⟨hMX, hVM, hR2, hQXM, hMR, hXR, hVs, hcardV, h3, hSyl, hMV, hVc⟩

end CFSG.Quasithin.H13.NQBlock
