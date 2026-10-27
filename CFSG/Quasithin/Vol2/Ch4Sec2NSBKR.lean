module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBDefs
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.InternalSecISec
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

private theorem mem_normalizer_inf_nsb2kr {G : Type} [Group G] {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_inf ⟨hA, hB⟩

private theorem exists_two_odd_split_nsb2kr {G : Type} [Group G] [Finite G] (S : Subgroup G)
    {x : G} (hx : x ∈ S) :
    ∃ y z : G, x = y * z ∧ y ∈ S ∧ z ∈ S ∧ (∃ a : ℕ, y ^ 2 ^ a = 1) ∧ Odd (orderOf z) := by
  obtain ⟨a, e, he, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hcop : IsCoprime ((2 ^ a : ℕ) : ℤ) (e : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr he))
  obtain ⟨u, v, huv⟩ := hcop
  have hy : (x ^ (v * (e : ℤ))) ^ 2 ^ a = 1 := by
    rw [← zpow_natCast, ← zpow_mul]
    have h2 : v * (e : ℤ) * ((2 ^ a : ℕ) : ℤ) = (orderOf x : ℤ) * v := by
      rw [hn]; push_cast; ring
    rw [h2, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  have hz : (x ^ (u * ((2 ^ a : ℕ) : ℤ))) ^ e = 1 := by
    rw [← zpow_natCast, ← zpow_mul]
    have h3 : u * ((2 ^ a : ℕ) : ℤ) * (e : ℤ) = (orderOf x : ℤ) * u := by
      rw [hn]; push_cast; ring
    rw [h3, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  refine ⟨x ^ (v * (e : ℤ)), x ^ (u * ((2 ^ a : ℕ) : ℤ)), ?_, S.zpow_mem hx _,
    S.zpow_mem hx _, ⟨a, hy⟩, Odd.of_dvd_nat he (orderOf_dvd_of_pow_eq_one hz)⟩
  rw [← zpow_add, add_comm, huv, zpow_one]

private theorem isPGroup_zpowers_nsb2kr {G : Type} [Group G] {y : G} {a : ℕ}
    (ha : y ^ 2 ^ a = 1) : IsPGroup 2 (Subgroup.zpowers y) := by
  refine IsPGroup.of_card_dvd_pow (n := a) ?_
  rw [Nat.card_zpowers]
  exact orderOf_dvd_of_pow_eq_one ha

private theorem mem_of_pow_two_pow_nsb2kr {G : Type} [Group G] {K : Subgroup G} {w : G} {e : ℕ}
    (hw : w ^ 2 ^ e ∈ K) (hodd : Odd (orderOf w)) : w ∈ K := by
  have hcop : Nat.Coprime (2 ^ e) (orderOf w) :=
    Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hodd)
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  have h := K.pow_mem hw j
  rwa [hj] at h

theorem kRInfGammaZero_of (h31 : Lemma31) (h32 : Lemma32) (hOdd : OddKGamma) :
    KRInfGammaZero := by
  intro G _ _ T M L Mm I H K m k hch hIV
  have hd : NoSumBigData G T M L Mm I H K m k := hch.1
  have hc : Conf4212 G T M L I H K := hd.2.2.1
  obtain ⟨hHK, -⟩ := h32 G T M L Mm I H K m k hd
  obtain ⟨hRlt, hRC⟩ := h31 G T M L Mm I H K m k hd
  have hRH : pCoreOf 2 I ≤ H := (pCoreOf_le 2 I).trans hc.inH.1
  have hKH : K ≤ H := le_of_mem_cComp hc.K_mem
  have hAH : K ⊔ pCoreOf 2 I ≤ H := _root_.sup_le hKH hRH
  have hRK : pCoreOf 2 I ≤ Subgroup.normalizer (K : Set G) := hRH.trans hHK
  have hRB : pCoreOf 2 I ≤ gammaZero T M L I := fun r hr =>
    ⟨⟨(hRlt.le hr).2, Subgroup.le_normalizer hr⟩, hRC (hRlt.le hr)⟩
  have hLHL : perfectCore (L ⊓ H) ≤ L := (perfectCore_le _).trans inf_le_left
  have hLO : pCoreOf 2 L ⊓ perfectCore (L ⊓ H) ≤ pCoreOf 2 (perfectCore (L ⊓ H)) :=
    le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun g hg => mem_normalizer_inf_nsb2kr
        (normalizer_le_normalizer_pCoreOf 2 L (Subgroup.le_normalizer (hLHL hg)))
        (Subgroup.le_normalizer hg))
      ((pCoreOf_isPGroup 2 L).to_le inf_le_left)
  have hC0 : ∀ x ∈ (K ⊔ pCoreOf 2 I) ⊓ gammaZero T M L I,
      x ∈ centralizerSection (H ⊓ M) (perfectCore (L ⊓ H)) (pCoreOf 2 (perfectCore (L ⊓ H))) := by
    intro x hx
    have hxH : x ∈ H := hAH hx.1
    have hxcs := mem_centralizerSection.mp hx.2.1.1
    have hxM : x ∈ M := hxcs.1
    have hxLH : x ∈ Subgroup.normalizer (perfectCore (L ⊓ H) : Set G) :=
      hc.LH_normal ⟨hxH, hxM⟩
    refine mem_centralizerSection.mpr ⟨⟨hxH, hxM⟩, hxLH,
      normalizer_le_normalizer_pCoreOf 2 (perfectCore (L ⊓ H)) hxLH, fun l hl => ?_⟩
    have h1 : l * x * l⁻¹ * x⁻¹ ∈ pCoreOf 2 L := hxcs.2.2.2 l (hLHL hl)
    have h3 : x * l⁻¹ * x⁻¹ ∈ perfectCore (L ⊓ H) :=
      (Subgroup.mem_normalizer_iff.mp hxLH l⁻¹).mp (Subgroup.inv_mem _ hl)
    have h2 : l * x * l⁻¹ * x⁻¹ ∈ perfectCore (L ⊓ H) := by
      have e : l * x * l⁻¹ * x⁻¹ = l * (x * l⁻¹ * x⁻¹) := by simp only [mul_assoc]
      rw [e]
      exact Subgroup.mul_mem _ hl h3
    exact hLO ⟨h1, h2⟩
  have hcc : conjClosure (perfectCore (L ⊓ H)) (H ⊓ M) = perfectCore (L ⊓ H) :=
    conjClosure_eq_self hc.LH_normal
  have hsyl := hc.hypC28.sylow
  rw [hcc] at hsyl
  obtain ⟨hRC0, -, hmax⟩ := isSylowTwoOf_iff_maximal.mp hsyl
  have hmain : ∀ x ∈ (K ⊔ pCoreOf 2 I) ⊓ gammaZero T M L I, x ∈ pCoreOf 2 I := by
    intro x hx
    obtain ⟨y, z, rfl, hy, hz, ⟨a, ha⟩, hodd⟩ :=
      exists_two_odd_split_nsb2kr ((K ⊔ pCoreOf 2 I) ⊓ gammaZero T M L I) hx
    have hyR : y ∈ pCoreOf 2 I := by
      have hX2 : IsPGroup 2 (Subgroup.zpowers y) := isPGroup_zpowers_nsb2kr ha
      have hzN : Subgroup.zpowers y ≤ Subgroup.normalizer (pCoreOf 2 I : Set G) :=
        Subgroup.zpowers_le.mpr hy.2.1.2
      have hPG : IsPGroup 2 ↥(pCoreOf 2 I ⊔ Subgroup.zpowers y) :=
        IsPGroup.to_sup_of_normal_left' (pCoreOf_isPGroup 2 I) hX2 hzN
      have hsub : pCoreOf 2 I ⊔ Subgroup.zpowers y ≤
          centralizerSection (H ⊓ M) (perfectCore (L ⊓ H)) (pCoreOf 2 (perfectCore (L ⊓ H))) :=
        _root_.sup_le hRC0 (Subgroup.zpowers_le.mpr (hC0 y hy))
      have hy' : y ∈ pCoreOf 2 I ⊔ Subgroup.zpowers y :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
      exact (hmax _ hsub hPG le_sup_left) hy'
    have hzK : z ∈ K := by
      obtain ⟨e, he⟩ :=
        CFSG.Quasithin.InternalSec.two_of_sup (pCoreOf_isPGroup 2 I) hRK z hz.1
      exact mem_of_pow_two_pow_nsb2kr he hodd
    have hz1 : z = 1 := hOdd G T M L Mm I H K m k hch hIV z ⟨hzK, hz.2⟩ hodd
    rw [hz1, mul_one]
    exact hyR
  exact le_antisymm (fun x hx => hmain x hx) (le_inf le_sup_right hRB)

end CFSG.Quasithin.H13.Ch4.NSB
