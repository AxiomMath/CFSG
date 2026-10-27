module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

theorem mem_zpowers_of_pow_three_ch615 {Q : Type*} [Group Q] [Finite Q] [IsCyclic Q] {w z : Q}
    (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) (hz3 : z ^ 3 = 1) : z ∈ Subgroup.zpowers w := by
  classical
  have := Fintype.ofFinite Q
  have hcard := IsCyclic.card_pow_eq_one_le (α := Q) (n := 3) (by norm_num)
  have hw2 : w ^ 2 ≠ 1 := by
    intro h
    apply hw1
    have : w = w ^ 3 * (w ^ 2)⁻¹ := by group
    rw [this, hw3, h, inv_one, one_mul]
  have hww : w ≠ w ^ 2 := by
    intro h
    apply hw1
    have : w = w ^ 2 * w⁻¹ := by group
    rw [this, ← h, mul_inv_cancel]
  by_contra hz
  have hz0 : z ≠ 1 := fun h => hz (h ▸ Subgroup.one_mem _)
  have hzw : z ≠ w := fun h => hz (h ▸ Subgroup.mem_zpowers w)
  have hzw2 : z ≠ w ^ 2 := fun h => hz (h ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers w) 2)
  have hsub : ({z, 1, w, w ^ 2} : Finset Q) ⊆ Finset.univ.filter (fun a : Q => a ^ 3 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl | rfl
    · exact hz3
    · exact one_pow 3
    · exact hw3
    · rw [← pow_mul, mul_comm, pow_mul, hw3, one_pow]
  have h4 : ({z, 1, w, w ^ 2} : Finset Q).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hww]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hw1.symm, hw2.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hz0, hzw, hzw2⟩
  have := Finset.card_le_card hsub
  omega

namespace Cx615C

theorem false_of_centralizes_ch615 (h432 : Stmt4_3_2) (c : Cx615C G T M L V H n) {z : G}
    (hzZ : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1)
    (hKz : oTwoUpper H ≤ Subgroup.centralizer ({z} : Set G)) {d : G} (hdB : d ∈ borelL T L)
    (hdodd : Odd (orderOf d)) (hd1 : d ≠ 1) (hdz : d * z * d⁻¹ = z) : False := by
  have h := c.hyp
  have hz := mem_quasithinOmegaOneCenter_iff.mp hzZ
  have hzd : z ∈ Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    calc d * z = d * z * d⁻¹ * d := by group
      _ = z * d := by rw [hdz]
  have hzL : z ∈ Subgroup.centralizer (L : Set G) := c.CZd d hdB hdodd hd1 ⟨hzZ, hzd⟩
  have hord : orderOf z = 2 := orderOf_eq_prime hz.2.2 hz1
  have hP2 : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hPne : Subgroup.zpowers z ≠ ⊥ := fun h0 => hz1 (by
    have := Subgroup.mem_zpowers z
    rw [h0] at this
    exact Subgroup.mem_bot.mp this)
  have hloc : IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers z : Set G)) :=
    ⟨_, hPne, hP2, rfl⟩
  have hTz : ∀ t ∈ T, t ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := fun t ht =>
    mem_normalizer_zpowers_ch615 (Subgroup.mem_centralizer_iff.mp hz.2.1 t ht)
  have hLT : L ⊔ T ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
    sup_le (fun l hl => mem_normalizer_zpowers_ch615 (Subgroup.mem_centralizer_iff.mp hzL l hl))
      hTz
  have hNM := le_of_isUniqueM_of_le_twoLocal (h.isUniqueM h432) hLT hloc
  have hsup : T ⊔ twoResidual H = H := sup_twoResidual_eq c.toCx615.isSylowTwoOf
  rw [twoResidual_eq_oTwoUpper'] at hsup
  apply c.hH.2.1
  rw [← hsup]
  refine sup_le (fun t ht => hNM (hTz t ht)) (fun k hk => hNM ?_)
  have hkz := Subgroup.mem_centralizer_iff.mp (hKz hk) z rfl
  exact mem_normalizer_zpowers_ch615 hkz.symm

theorem mem_zpowers_of_autI_borelL_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H)) {x y : MulAut (IntMod (UX615 T L H) hU)}
    (hx : x ∈ autI hU (borelL T L)) (hy : y ∈ autI hU (borelL T L)) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1) : y ∈ Subgroup.zpowers x := by
  classical
  have h := c.hyp.toHyp5_0_1
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hBN : borelL T L ≤ Subgroup.normalizer (UX615 T L H : Set G) := le_sup_left.trans hXN
  have hDN : D ≤ Subgroup.normalizer (UX615 T L H : Set G) := hD.1.trans hBN
  have hSN : T ⊓ L ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    (Hyp5_0_1.inf_le_borel T L).trans hBN
  set Bs := autI hU (borelL T L) with hBs
  set A := autI hU (T ⊓ L) with hA
  set Ds := autI hU D with hDs
  have hBeq : Bs = Ds ⊔ A := by rw [hBs, ← h.borelL_eq_sup hD, autI_sup hU hDN hSN]
  have hAB : A ≤ Bs := autI_mono hU (Hyp5_0_1.inf_le_borel T L)
  have hBA : Bs ≤ Subgroup.normalizer (A : Set (MulAut _)) := fun b hb =>
    Subgroup.mem_normalizer_iff.mpr fun a => ⟨fun ha => C124.autI_conj_mem hU
      (inf_le_right : borelL T L ≤ _) b hb a ha, fun ha => by
        have := C124.autI_conj_mem hU (inf_le_right : borelL T L ≤ _) b⁻¹ (Bs.inv_mem hb) _ ha
        simpa [mul_assoc] using this⟩
  have hA2 : IsPGroup 2 ↥A := by
    have hT2 : IsPGroup 2 ↥(T ⊓ L) := c.hyp.sylow.1.to_le inf_le_left
    rw [hA, ← range_convHom hU _ hSN]
    exact hT2.of_surjective _ (convHom hU _ hSN).rangeRestrict_surjective
  have hAn : (A.subgroupOf Bs).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAB).mpr hBA
  set mk := QuotientGroup.mk' (A.subgroupOf Bs) with hmk
  have hDcyc : IsCyclic ↥Ds := (c.autI_hall_ch615 hU hD).1
  have hDB : Ds ≤ Bs := autI_mono hU hD.1
  have hsurj : Function.Surjective (mk.comp (Subgroup.inclusion hDB)) := by
    intro q
    obtain ⟨⟨b, hb⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hb' : b ∈ ((Ds ⊔ A : Subgroup _) : Set (MulAut _)) := by rw [← hBeq]; exact hb
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Ds A (hDB.trans hBA)] at hb'
    obtain ⟨δ, hδ, a, ha, rfl⟩ := hb'
    refine ⟨⟨δ, hδ⟩, ?_⟩
    simp only [MonoidHom.comp_apply, hmk, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    show (⟨δ, hDB hδ⟩ : ↥Bs)⁻¹ * ⟨δ * a, hb⟩ ∈ A.subgroupOf Bs
    rw [Subgroup.mem_subgroupOf]
    simpa using ha
  have hQcyc : IsCyclic (↥Bs ⧸ A.subgroupOf Bs) := isCyclic_of_surjective _ hsurj
  have hker : ∀ g : ↥Bs, g.1 ^ 3 = 1 → mk g = 1 → g = 1 := by
    intro g hg3 hg1
    have hgA : g.1 ∈ A := by
      have := (QuotientGroup.eq_one_iff (N := A.subgroupOf Bs) g).mp hg1
      exact Subgroup.mem_subgroupOf.mp this
    obtain ⟨k, hk⟩ := hA2 ⟨g, hgA⟩
    have hk' : g.1 ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have h1 : orderOf g.1 = 1 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hg3) hcop)
      (orderOf_dvd_of_pow_eq_one hk')
    exact Subtype.ext (orderOf_eq_one_iff.mp h1)
  set x' : ↥Bs := ⟨x, hx⟩
  set y' : ↥Bs := ⟨y, hy⟩
  have hx'3 : x' ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hy'3 : y' ^ 3 = 1 := Subtype.ext (by simpa using hy3)
  have hmx1 : mk x' ≠ 1 := fun h1 => hx1 (congrArg Subtype.val (hker x' hx3 h1))
  have hmx3 : mk x' ^ 3 = 1 := by rw [← map_pow, hx'3, map_one]
  have hmy3 : mk y' ^ 3 = 1 := by rw [← map_pow, hy'3, map_one]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_pow_three_ch615 hmx3 hmx1 hmy3)
  have hcomm : x' * y' = y' * x' := Subtype.ext hxy
  have hyx3 : (y' * (x' ^ k)⁻¹) ^ 3 = 1 := by
    have hc : Commute y' (x' ^ k)⁻¹ := (Commute.zpow_right (hcomm.symm : Commute y' x') k).inv_right
    rw [hc.mul_pow, hy'3, one_mul, inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hx'3, one_zpow, inv_one]
  have hyx1 : mk (y' * (x' ^ k)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
  have := hker _ (by simpa using congrArg Subtype.val hyx3) hyx1
  have hyk : y' = x' ^ k := by
    rw [mul_inv_eq_one] at this
    exact this
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using (congrArg Subtype.val hyk).symm⟩

end Cx615C

end CFSG.Quasithin.H13
