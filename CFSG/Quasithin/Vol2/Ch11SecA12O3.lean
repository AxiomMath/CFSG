module

public import CFSG.Quasithin.Vol2.Ch11SecA02Quot
public import CFSG.Quasithin.Background.A3Structure318Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Quasithin
open scoped Pointwise

variable {H : Type} [Group H] [Finite H]

theorem pPrimeCore_le_of_sup {K A : Subgroup H} [K.Normal] (hsup : K ⊔ A = ⊤)
    (hA : IsPGroup 3 A) : CFSG.pPrimeCore 3 H ≤ K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro y hy
  have hyKA : y ∈ (K : Set H) * (A : Set H) := by
    rw [← Subgroup.normal_mul K A, hsup]
    exact Subgroup.mem_top y
  obtain ⟨k, hk, a, ha, rfl⟩ := hyKA
  have hρk : QuotientGroup.mk' K k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
  have h1 : orderOf (QuotientGroup.mk' K a) ∣ orderOf (k * a) := by
    have := orderOf_map_dvd (QuotientGroup.mk' K) (k * a)
    rwa [map_mul, hρk, one_mul] at this
  obtain ⟨m, hm⟩ := hA ⟨a, ha⟩
  have h2 : orderOf (QuotientGroup.mk' K a) ∣ 3 ^ m := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← map_pow]
    have : a ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
    rw [this, map_one]
  have hco : Nat.Coprime (3 ^ m) (orderOf (k * a)) :=
    Nat.Coprime.pow_left m (CFSG.pPrimeCore_coprime_card.coprime_dvd_right
      (Subgroup.orderOf_dvd_natCard _ hy))
  have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hco) h1
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact K.mul_mem hk h3

omit [Finite H] in
theorem map_pCore_le_pCore (K : Subgroup H) [K.Normal] :
    (CFSG.pCore 2 ↥K).map K.subtype ≤ CFSG.pCore 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : ((CFSG.pCore 2 ↥K).map K.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  exact le_sSup ⟨hn, CFSG.pCore_isPGroup.map K.subtype⟩

theorem pPrimeCore_three_eq {K A : Subgroup H} [K.Normal] (hsup : K ⊔ A = ⊤)
    (hA : IsPGroup 3 A) (hQ : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hZ : Nat.card (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) ∣ 3)
    (h3 : 3 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) :
    CFSG.pPrimeCore 3 H = (CFSG.pCore 2 ↥K).map K.subtype ∧
      CFSG.pCore 2 H = (CFSG.pCore 2 ↥K).map K.subtype := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOK : CFSG.pPrimeCore 3 H ≤ K := pPrimeCore_le_of_sup hsup hA
  have hO'n : ((CFSG.pPrimeCore 3 H).subgroupOf K).Normal :=
    Subgroup.Normal.subgroupOf CFSG.pPrimeCore_normal K
  set M := ((CFSG.pPrimeCore 3 H).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
    with hM
  have hMn : M.Normal := Subgroup.Normal.map hO'n _ (QuotientGroup.mk'_surjective _)
  have hcardO' : Nat.card ↥((CFSG.pPrimeCore 3 H).subgroupOf K) =
      Nat.card ↥(CFSG.pPrimeCore 3 H) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOK).toEquiv
  have hMc : Nat.Coprime 3 (Nat.card M) :=
    CFSG.pPrimeCore_coprime_card.coprime_dvd_right
      ((Subgroup.card_map_dvd _ _).trans hcardO'.dvd)
  have hMt : M ≠ ⊤ := by
    intro ht
    rw [ht, Subgroup.card_top] at hMc
    exact absurd (Nat.Coprime.eq_one_of_dvd hMc h3) (by norm_num)
  have hMZ := le_center_of_normal_ne_top hQ hMt
  have hMb : M = ⊥ := by
    have h1 : Nat.card M ∣ 3 := (Subgroup.card_dvd_of_le hMZ).trans hZ
    exact Subgroup.card_eq_one.mp (Nat.Coprime.eq_one_of_dvd hMc.symm h1)
  have hO'le : (CFSG.pPrimeCore 3 H).subgroupOf K ≤ CFSG.pCore 2 ↥K := by
    intro x hx
    have hx' : QuotientGroup.mk' (CFSG.pCore 2 ↥K) x ∈ M := ⟨x, hx, rfl⟩
    rwa [hMb, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
  have hOle : CFSG.pPrimeCore 3 H ≤ (CFSG.pCore 2 ↥K).map K.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hOK]
    exact Subgroup.map_mono hO'le
  have hP2 : CFSG.pCore 2 H ≤ CFSG.pPrimeCore 3 H := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := H))
    refine le_sSup ⟨inferInstance, ?_⟩
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hPK := map_pCore_le_pCore K
  exact ⟨le_antisymm hOle (hPK.trans hP2), le_antisymm (hP2.trans hOle) hPK⟩

omit [Finite H] in
theorem starImage_mulEquiv {K : Subgroup H}
    (hO : CFSG.pPrimeCore 3 H = (CFSG.pCore 2 ↥K).map K.subtype) :
    Nonempty (↥(starImage 3 K) ≃* (↥K ⧸ CFSG.pCore 2 ↥K)) := by
  set f : ↥K →* PStar 3 H := (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)).comp K.subtype with hf
  have hker : f.ker = CFSG.pCore 2 ↥K := by
    rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', hO,
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  have hrange : f.range = starImage 3 K := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨((MulEquiv.subgroupCongr hrange).symm.trans
    (QuotientGroup.quotientKerEquivRange f).symm).trans (QuotientGroup.quotientMulEquivOfEq hker)⟩

end CFSG.Quasithin.Vol2.Ch11.SecA
