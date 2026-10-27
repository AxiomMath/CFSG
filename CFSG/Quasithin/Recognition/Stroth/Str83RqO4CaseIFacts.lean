module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Defs
public import CFSG.Quasithin.Recognition.St84.Sec6NatQuot
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dictionary
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.Stroth.G5
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem cif_commutator_eq_one {e k : G} (h : k * e * k⁻¹ = e) : ⁅e, k⁆ = 1 := by
  have hke : k * e = e * k := by
    calc k * e = k * e * k⁻¹ * k := by group
      _ = e * k := by rw [h]
  rw [commutatorElement_def, ← hke]
  group

private theorem cif_surj {Z : Subgroup G} {k : G}
    (hZc : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) (hk : k ∈ normalizer (Z : Set G))
    (hfix : ∀ z ∈ Z, k * z * k⁻¹ = z → z = 1) {w : G} (hw : w ∈ Z) :
    ∃ z ∈ Z, k * z * k⁻¹ * z⁻¹ = w := by
  have hconj : ∀ z ∈ Z, k * z * k⁻¹ ∈ Z := fun z hz => (mem_normalizer_iff.mp hk z).mp hz
  let φ : Z → Z := fun z => ⟨k * z * k⁻¹ * (z : G)⁻¹, Z.mul_mem (hconj z z.2) (Z.inv_mem z.2)⟩
  have hinj : Function.Injective φ := by
    intro z w hzw
    have h : k * (z : G) * k⁻¹ * (z : G)⁻¹ = k * (w : G) * k⁻¹ * (w : G)⁻¹ :=
      congrArg Subtype.val hzw
    have hu : (z : G) * (w : G)⁻¹ ∈ Z := Z.mul_mem z.2 (Z.inv_mem w.2)
    have ha : k * (w : G) * k⁻¹ ∈ Z := hconj w w.2
    have hb : (w : G)⁻¹ * z ∈ Z := Z.mul_mem (Z.inv_mem w.2) z.2
    have hab := hZc _ ha _ hb
    have hwz := hZc _ (Z.inv_mem w.2) _ z.2
    have h1 : k * (z : G) * k⁻¹ = (k * (w : G) * k⁻¹) * ((w : G)⁻¹ * z) := by
      calc k * (z : G) * k⁻¹ = (k * (z : G) * k⁻¹ * (z : G)⁻¹) * z := by group
        _ = (k * (w : G) * k⁻¹ * (w : G)⁻¹) * z := by rw [h]
        _ = _ := by group
    have hfixu : k * ((z : G) * (w : G)⁻¹) * k⁻¹ = (z : G) * (w : G)⁻¹ := by
      calc k * ((z : G) * (w : G)⁻¹) * k⁻¹
          = (k * (z : G) * k⁻¹) * (k * (w : G) * k⁻¹)⁻¹ := by group
        _ = (k * (w : G) * k⁻¹) * ((w : G)⁻¹ * z) * (k * (w : G) * k⁻¹)⁻¹ := by rw [h1]
        _ = ((w : G)⁻¹ * z) * (k * (w : G) * k⁻¹) * (k * (w : G) * k⁻¹)⁻¹ := by rw [hab]
        _ = (w : G)⁻¹ * z := by group
        _ = (z : G) * (w : G)⁻¹ := hwz
    exact Subtype.ext (mul_inv_eq_one.mp (hfix _ hu hfixu))
  obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨w, hw⟩
  exact ⟨z, z.2, congrArg Subtype.val hz⟩

theorem caseI_of_centerOf_LX_eq_QT {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hnat : St84.NatQuot (t.LX t.QT 1) (t.EX t.QT 1) (centerOf (t.LX t.QT 1)) f)
    (hD2 : t.D2 ≤ t.YX t.QT 1) (h0 : t.Zv 0 ⊓ t.QT = ⊥) (h1 : t.Zv 1 ⊓ t.QT = ⊥)
    (hZ1 : t.Zv 1 ≤ t.EX t.QT 1)
    (hEE : t.EX t.QT 1 ⊓ t.EX t.QT (-1) = centerOf (t.PX t.QT))
    (hQZ : t.QT ≤ centerOf (t.PX t.QT)) (hZ0 : t.Zv 0 ≤ centerOf (t.PX t.QT))
    (hidx : (t.EX t.QT 1).relIndex (t.PX t.QT) = 2 ^ f)
    (hcomm : ⁅t.EX t.QT 1, t.PX t.QT⁆ ≤ centerOf (t.PX t.QT))
    (hA : centerOf (t.LX t.QT 1) = t.QT)
    (hfpf : ∀ k ∈ t.D2, k ≠ 1 → ∀ e ∈ t.EX t.QT 1,
      ⁅e, k⁆ ∈ centerOf (t.LX t.QT 1) → e ∈ centerOf (t.LX t.QT 1))
    (htr : ∀ x ∈ centerOf (t.PX t.QT), x ∉ centerOf (t.LX t.QT 1) →
      ∀ y ∈ centerOf (t.PX t.QT), y ∉ centerOf (t.LX t.QT 1) →
        ∃ k ∈ t.D2, k * x * k⁻¹ * y⁻¹ ∈ centerOf (t.LX t.QT 1)) :
    t.EX t.QT 1 ⊓ t.Qv (-1) ≤ t.Zv 0 ⊔ t.QT ∧ t.Zv 0 ≤ t.Zv 1 ∧
      (∀ x ∈ t.Qv 0, ∀ z ∈ t.Zv 1, x * z * x⁻¹ * z⁻¹ ∈ t.Zv 0) ∧
      (∀ e ∈ t.EX t.QT 1, (∀ l ∈ t.LX t.QT 1, Odd (orderOf l) → l * e * l⁻¹ = e) →
        e ∈ t.QT) := by
  rw [hA] at hfpf htr
  have hD2card : Nat.card t.D2 = 2 ^ f - 1 := t.card_D2 hfr
  have hpow : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hfr.hf
  haveI : Nontrivial t.D2 := by
    rw [← Finite.one_lt_card_iff_nontrivial, hD2card]
    omega
  obtain ⟨⟨k, hkD⟩, hk1⟩ := exists_ne (1 : t.D2)
  have hk1' : k ≠ 1 := fun h => hk1 (Subtype.ext h)
  have hkK : k ∈ t.K := (le_sup_right : t.D2 ≤ t.K) hkD
  have hkL : k ∈ t.LX t.QT 1 := oTwoRes_le _ (hD2 hkD)
  have hkQ : ∀ q ∈ t.QT, k * q * k⁻¹ = q := by
    intro q hq
    have hq' : q ∈ t.LX t.QT 1 ⊓ centralizer (t.LX t.QT 1 : Set G) := by
      rw [← hA] at hq
      exact hq
    rw [Subgroup.mem_centralizer_iff.mp hq'.2 k hkL, mul_inv_cancel_right]
  have hkodd : Odd (orderOf k) := by
    have hdvd := Subgroup.orderOf_dvd_natCard t.D2 hkD
    rw [hD2card] at hdvd
    refine Odd.of_dvd_nat ?_ hdvd
    have h2 : 2 ^ f = 2 * 2 ^ (f - 1) := by
      rw [← pow_succ']
      congr 1
      have := hfr.hf
      omega
    have h1' : 1 ≤ 2 ^ (f - 1) := Nat.one_le_two_pow
    exact ⟨2 ^ (f - 1) - 1, by omega⟩
  have hkZ0 : k ∈ normalizer (t.Zv 0 : Set G) := t.K_le_normalizer_Zv 0 hkK
  have hkZ1 : k ∈ normalizer (t.Zv 1 : Set G) := t.K_le_normalizer_Zv 1 hkK
  have hc4 : ∀ e ∈ t.EX t.QT 1, (∀ l ∈ t.LX t.QT 1, Odd (orderOf l) → l * e * l⁻¹ = e) →
      e ∈ t.QT := by
    intro e he hfix
    refine hfpf k hkD hk1' e he ?_
    rw [cif_commutator_eq_one (hfix k hkL hkodd)]
    exact one_mem _
  have hQE : t.QT ≤ t.EX t.QT 1 := (le_of_eq hA.symm).trans hnat.Z_le
  have hLN : t.LX t.QT 1 ≤ normalizer (t.QT : Set G) := (oTwoPrime_le _).trans inf_le_left
  have hLG : t.LX t.QT 1 ≤ t.Gv 1 := (oTwoPrime_le _).trans inf_le_right
  have hE1 : t.Zv 1 ⊔ t.QT = t.EX t.QT 1 := by
    rcases hnat.irred (t.Zv 1 ⊔ t.QT) ((le_of_eq hA).trans le_sup_right) (sup_le hZ1 hQE)
      (F1.le_normalizer_sup (hLG.trans (t.Gv_le_normalizer_Zv 1)) hLN) with h | h
    · exfalso
      rw [hA] at h
      have hle : t.Zv 1 ≤ t.QT := le_sup_left.trans h.le
      exact t.Zv_ne_bot hfr.hF 1 (by rw [← inf_eq_left.mpr hle]; exact h1)
    · exact h
  have hZPE : centerOf (t.PX t.QT) ≤ t.EX t.QT 1 := (le_of_eq hEE.symm).trans inf_le_left
  have hZ1N : t.Zv 1 ≤ normalizer (t.QT : Set G) := hZ1.trans inf_le_right
  have hdec : ∀ x ∈ t.EX t.QT 1, ∃ z ∈ t.Zv 1, ∃ q ∈ t.QT, z * q = x := by
    intro x hx
    rw [← hE1] at hx
    have hx' : x ∈ ((t.Zv 1 : Set G) * (t.QT : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZ1N]
      exact hx
    obtain ⟨z, hz, q, hq, rfl⟩ := hx'
    exact ⟨z, hz, q, hq, rfl⟩
  have hZ0c : ∀ x ∈ t.Zv 0, ∀ y ∈ t.Zv 0, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (t.Zv_le_centralizer 0 hy) x (t.Zv_le_Qv 0 hx)
  have hfix0 : ∀ z ∈ t.Zv 0, k * z * k⁻¹ = z → z = 1 := by
    intro z hz hkz
    have hzQ : z ∈ t.QT := by
      refine hfpf k hkD hk1' z (hZPE (hZ0 hz)) ?_
      rw [cif_commutator_eq_one hkz]
      exact one_mem _
    have hm : z ∈ t.Zv 0 ⊓ t.QT := ⟨hz, hzQ⟩
    rw [h0] at hm
    exact Subgroup.mem_bot.mp hm
  have hZ0Z1 : t.Zv 0 ≤ t.Zv 1 := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := cif_surj hZ0c hkZ0 hfix0 hw
    obtain ⟨c, hc, q, hq, rfl⟩ := hdec z (hZPE (hZ0 hz))
    have hqk : q * k⁻¹ * q⁻¹ = k⁻¹ := by
      calc q * k⁻¹ * q⁻¹ = k⁻¹ * (k * q * k⁻¹) * q⁻¹ := by group
        _ = k⁻¹ := by rw [hkQ q hq]; group
    have heq : k * (c * q) * k⁻¹ * (c * q)⁻¹ = k * c * k⁻¹ * c⁻¹ := by
      calc k * (c * q) * k⁻¹ * (c * q)⁻¹ = k * c * (q * k⁻¹ * q⁻¹) * c⁻¹ := by group
        _ = k * c * k⁻¹ * c⁻¹ := by rw [hqk]
    rw [heq]
    exact (t.Zv 1).mul_mem ((mem_normalizer_iff.mp hkZ1 c).mp hc) ((t.Zv 1).inv_mem hc)
  have hC : ∀ c ∈ t.Zv 1, c ∈ centerOf (t.PX t.QT) → c ∈ t.Zv 0 := by
    intro c hc1 hcP
    by_cases hcQ : c ∈ t.QT
    · have hm : c ∈ t.Zv 1 ⊓ t.QT := ⟨hc1, hcQ⟩
      rw [h1] at hm
      rw [Subgroup.mem_bot.mp hm]
      exact one_mem _
    · obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (t.Zv_ne_bot hfr.hF 0)
      have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
      have hzQ : z ∉ t.QT := fun hzQ => by
        have hm : z ∈ t.Zv 0 ⊓ t.QT := ⟨hz, hzQ⟩
        rw [h0] at hm
        exact hz1' (Subgroup.mem_bot.mp hm)
      obtain ⟨k', hk'D, hk'⟩ := htr z (hZ0 hz) hzQ c hcP hcQ
      have hk'K : k' ∈ t.K := (le_sup_right : t.D2 ≤ t.K) hk'D
      have hw0 : k' * z * k'⁻¹ ∈ t.Zv 0 :=
        (mem_normalizer_iff.mp (t.K_le_normalizer_Zv 0 hk'K) z).mp hz
      have hm : k' * z * k'⁻¹ * c⁻¹ ∈ t.Zv 1 ⊓ t.QT :=
        ⟨(t.Zv 1).mul_mem (hZ0Z1 hw0) ((t.Zv 1).inv_mem hc1), hk'⟩
      rw [h1] at hm
      rw [(mul_inv_eq_one.mp (Subgroup.mem_bot.mp hm)).symm]
      exact hw0
  have hc1 : t.EX t.QT 1 ⊓ t.Qv (-1) ≤ t.Zv 0 ⊔ t.QT := by
    rintro x ⟨hxE, hxQ⟩
    have hxP : x ∈ centerOf (t.PX t.QT) := by
      rw [← hEE]
      exact ⟨hxE, hxQ, hxE.2⟩
    obtain ⟨c, hc, q, hq, rfl⟩ := hdec x hxE
    have hcP : c ∈ centerOf (t.PX t.QT) := by
      have hcq : c = c * q * q⁻¹ := by group
      rw [hcq]
      exact (centerOf _).mul_mem hxP ((centerOf _).inv_mem (hQZ hq))
    exact Subgroup.mul_mem_sup (hC c hc hcP) hq
  have hPG1 : t.PX t.QT ≤ t.Gv 1 := inf_le_right.trans inf_le_right
  have hPN : t.PX t.QT ≤ normalizer (t.Qv 1 : Set G) := hPG1.trans (t.Gv_le_normalizer_Qv 1)
  have hQ0S : t.Qv 0 ≤ S := by
    rw [t.Qv_zero]
    exact Q1_le_S hfr.hF
  have hQ1S : t.Qv 1 ≤ S := by
    rw [t.Qv_one]
    exact Q2_le_S hfr.hF
  have hQS : (t.Qv 1).relIndex S = 2 ^ f := by
    have h := (t.relIndex_Qv_pCoreOf hfr 1).1
    rw [sub_self, t.pCoreOf_Gw_zero_one hfr, if_neg Int.not_even_one] at h
    exact h
  have hrel : (t.PX t.QT ⊓ t.Qv 1).relIndex (t.PX t.QT) = 2 ^ f := by
    rw [← hidx]
    unfold Subgroup.relIndex
    congr 1
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro hy
      exact ⟨hy.2, y.2.2.1⟩
    · intro hy
      exact ⟨y.2, hy.1⟩
  have hSle : S ≤ t.PX t.QT ⊔ t.Qv 1 := by
    have hm := Subgroup.relIndex_mul_relIndex (H := t.Qv 1) (K := t.PX t.QT ⊔ t.Qv 1) (L := S)
      le_sup_right (sup_le (inf_le_left.trans hQ0S) hQ1S)
    rw [(CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hPN).2, hrel, hQS] at hm
    have h2 : 0 < 2 ^ f := by positivity
    exact Subgroup.relIndex_eq_one.mp (Nat.eq_of_mul_eq_mul_left h2 (hm.trans (mul_one _).symm))
  have hc3 : ∀ x ∈ t.Qv 0, ∀ z ∈ t.Zv 1, x * z * x⁻¹ * z⁻¹ ∈ t.Zv 0 := by
    intro x hx z hz
    have hx' : x ∈ ((t.PX t.QT : Set G) * (t.Qv 1 : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hPN]
      exact hSle (hQ0S hx)
    obtain ⟨p, hp, q, hq, rfl⟩ := hx'
    have hqz : q * z = z * q :=
      Subgroup.mem_centralizer_iff.mp (t.Zv_le_centralizer 1 hz) q hq
    have heq : p * q * z * (p * q)⁻¹ * z⁻¹ = (z * p * z⁻¹ * p⁻¹)⁻¹ := by
      calc p * q * z * (p * q)⁻¹ * z⁻¹ = p * (q * z) * q⁻¹ * p⁻¹ * z⁻¹ := by group
        _ = p * (z * q) * q⁻¹ * p⁻¹ * z⁻¹ := by rw [hqz]
        _ = (z * p * z⁻¹ * p⁻¹)⁻¹ := by group
    rw [heq]
    refine hC _ ?_ ?_
    · have hpN : p ∈ normalizer (t.Zv 1 : Set G) := t.Gv_le_normalizer_Zv 1 (hPG1 hp)
      have hre : z * p * z⁻¹ * p⁻¹ = z * (p * z⁻¹ * p⁻¹) := by group
      rw [hre]
      exact (t.Zv 1).inv_mem ((t.Zv 1).mul_mem hz
        ((mem_normalizer_iff.mp hpN _).mp ((t.Zv 1).inv_mem hz)))
    · have hmem : z * p * z⁻¹ * p⁻¹ ∈ ⁅t.EX t.QT 1, t.PX t.QT⁆ := by
        have := Subgroup.commutator_mem_commutator (hZ1 hz) hp
        rwa [commutatorElement_def] at this
      exact (centerOf _).inv_mem (hcomm hmem)
  exact ⟨hc1, hZ0Z1, hc3, hc4⟩

end Track

end CFSG.Quasithin.Stroth.Rq
