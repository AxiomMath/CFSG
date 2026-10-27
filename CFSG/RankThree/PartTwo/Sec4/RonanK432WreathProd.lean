module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Wreath

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.RankThree.PartTwo.Sec4.Item434Kit Subgroup
open scoped Pointwise

theorem commute_baseA_of_commute_z {S : Type} [Group S] {z : Fin 3 → S} {e : S}
    (hec : ∀ i, z i * e = e * z i) : ∀ a ∈ baseA z, a * e = e * a := by
  intro a ha
  have : baseA z ≤ Subgroup.centralizer ({e} : Set S) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · refine zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hec 0)
    · refine zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hec 1)
    · refine zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hec 2)
  exact Subgroup.mem_centralizer_singleton_iff.mp (this ha)

theorem commute_wreathW_of_commute {S : Type} [Group S] {z : Fin 3 → S} {t e : S}
    (hec : ∀ i, z i * e = e * z i) (het : t * e = e * t) : ∀ w ∈ wreathW z t, w * e = e * w := by
  intro w hw
  have : wreathW z t ≤ Subgroup.centralizer ({e} : Set S) := by
    refine sup_le ?_ ?_
    · intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact commute_baseA_of_commute_z hec a ha
    · refine zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact het
  exact Subgroup.mem_centralizer_singleton_iff.mp (this hw)

theorem mem_sup_zpowers_of_commute {S : Type} [Group S] {W : Subgroup S} {e : S}
    (hWe : ∀ w ∈ W, w * e = e * w) {x : S} (hx : x ∈ W ⊔ zpowers e) :
    ∃ w ∈ W, ∃ k : ℤ, x = w * e ^ k := by
  have hle : zpowers e ≤ normalizer (W : Set S) := by
    refine zpowers_le.mpr ?_
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have h3 : e * y * e⁻¹ = y := by rw [← hWe y hy]; group
      rw [h3]; exact hy
    · intro hy
      have hy' := hWe (e * y * e⁻¹) hy
      have h1 : e * y = e * (e * y * e⁻¹) := by
        calc e * y = (e * y * e⁻¹) * e := by group
          _ = e * (e * y * e⁻¹) := hy'
      have h2 : y = e * y * e⁻¹ := mul_left_cancel h1
      rw [h2]; exact hy
  have hx' : x ∈ ((W : Set S) * (zpowers e : Set S)) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hle]
    exact hx
  obtain ⟨w, hw, b, hb, rfl⟩ := hx'
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
  exact ⟨w, hw, k, rfl⟩

theorem isPGroup_sup_zpowers {S : Type} [Group S] {W : Subgroup S} {e : S} (hW : IsPGroup 3 W)
    (he3 : e ^ 3 = 1) (hWe : ∀ w ∈ W, w * e = e * w) : IsPGroup 3 (W ⊔ zpowers e : Subgroup S) := by
  intro x
  obtain ⟨w, hw, k, hx⟩ := mem_sup_zpowers_of_commute hWe x.2
  obtain ⟨n, hn⟩ := hW ⟨w, hw⟩
  refine ⟨n + 1, Subtype.ext ?_⟩
  have hwn : w ^ (3 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  have hc : Commute w (e ^ k) := by
    refine (show Commute w e from hWe w hw).zpow_right k
  have h1 : ((x : S)) ^ (3 ^ (n + 1)) = w ^ (3 ^ (n + 1)) * (e ^ k) ^ (3 ^ (n + 1)) := by
    rw [hx]; exact hc.mul_pow _
  have h2 : w ^ (3 ^ (n + 1)) = 1 := by
    rw [pow_succ, pow_mul, hwn, one_pow]
  have h3 : (e ^ k) ^ (3 ^ (n + 1)) = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have : e ^ ((3 ^ (n + 1) : ℕ) : ℤ) = 1 := by
      rw [zpow_natCast, pow_succ, mul_comm, pow_mul, he3, one_pow]
    rw [this, one_zpow]
  show ((x : S)) ^ (3 ^ (n + 1)) = 1
  rw [h1, h2, h3, one_mul]

theorem card_wreathW_eq_eighty_one {S : Type} [Group S] [Finite S] {z : Fin 3 → S} {t : S}
    (hf : WreathFacts z t) : Nat.card (wreathW z t) = 81 := by
  refine le_antisymm ?_ (le_card_wreathW hf)
  let f : ((Fin 3 → ZMod 3) × Fin 3) → wreathW z t := fun p =>
    ⟨vecElt z p.1 * t ^ (p.2 : ℕ),
      (wreathW z t).mul_mem (mem_sup_left (vecElt_mem_baseA hf p.1))
        ((wreathW z t).pow_mem t_mem_wreathW _)⟩
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨v, j, hx⟩ := mem_wreathW hf x.2
    exact ⟨(v, j), Subtype.ext hx.symm⟩
  calc Nat.card (wreathW z t) ≤ Nat.card ((Fin 3 → ZMod 3) × Fin 3) :=
        Nat.card_le_card_of_surjective f hsurj
    _ = 81 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
        norm_num

theorem three_dvd_of_pow_mem {S : Type} [Group S] {A : Subgroup S} {e : S} (he3 : e ^ 3 = 1)
    (heA : e ∉ A) {j : ℤ} (hj : e ^ j ∈ A) : (3 : ℤ) ∣ j := by
  by_contra h3
  apply heA
  have hjj : j * j % 3 = 1 := by
    have : j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases this with h | h <;> simp [Int.mul_emod, h]
  have : e ^ (j * j) = e := by
    rw [zpow_eq_zpow_mod_three_of_pow_three he3, hjj, zpow_one]
  rw [← this, zpow_mul]
  exact A.zpow_mem hj j

theorem zpow_eq_one_of_dvd_three {S : Type} [Group S] {e : S} (he3 : e ^ 3 = 1) {j : ℤ}
    (hj : (3 : ℤ) ∣ j) : e ^ j = 1 := by
  obtain ⟨l, rfl⟩ := hj
  rw [zpow_mul]
  have : e ^ (3 : ℤ) = 1 := by exact_mod_cast he3
  rw [this, one_zpow]

theorem wreath_prod_flip {S : Type} [Group S] {z : Fin 3 → S} {t e m : S}
    (hf : WreathFacts z t) (he3 : e ^ 3 = 1) (hec : ∀ i, z i * e = e * z i)
    (heA : e ∉ baseA z)
    (hm0 : m * z 0 * m⁻¹ = (z 0)⁻¹) (hm1 : m * z 1 * m⁻¹ = z 1) (hm2 : m * z 2 * m⁻¹ = z 2)
    (hme : m * e * m⁻¹ = e) (a k : ℤ) (ha3 : ¬ (3 : ℤ) ∣ a) :
    (m * (vecElt z ![1, 1, 1] ^ a * e ^ k) * m⁻¹) * (vecElt z ![1, 1, 1] ^ a * e ^ k) =
      (vecElt z ![1, 1, 1] ^ a * e ^ k) * (m * (vecElt z ![1, 1, 1] ^ a * e ^ k) * m⁻¹) ∧
    m * (vecElt z ![1, 1, 1] ^ a * e ^ k) * m⁻¹ ∉
      Subgroup.zpowers (vecElt z ![1, 1, 1] ^ a * e ^ k) := by
  haveI : IsMulCommutative (baseA z) := (isElemAbelian_baseA hf).1
  set c := vecElt z ![1, 1, 1] with hc
  have h1v : ((1 : ZMod 3)).val = 1 := rfl
  have h2v : ((2 : ZMod 3)).val = 2 := rfl
  have hcdef : c = z 0 * z 1 * z 2 := by simp [hc, vecElt, h1v]
  set c' : S := (z 0)⁻¹ * z 1 * z 2 with hc'
  have hc'A : c' ∈ baseA z :=
    (baseA z).mul_mem ((baseA z).mul_mem ((baseA z).inv_mem (z_mem_baseA 0)) (z_mem_baseA 1))
      (z_mem_baseA 2)
  have hcA : c ∈ baseA z := vecElt_mem_baseA hf _
  have hmc : m * c * m⁻¹ = c' := by
    rw [hcdef, hc']
    calc m * (z 0 * z 1 * z 2) * m⁻¹
        = (m * z 0 * m⁻¹) * (m * z 1 * m⁻¹) * (m * z 2 * m⁻¹) := by group
      _ = (z 0)⁻¹ * z 1 * z 2 := by rw [hm0, hm1, hm2]
  have hmu : m * (c ^ a * e ^ k) * m⁻¹ = c' ^ a * e ^ k := by
    have h1 : m * (c ^ a * e ^ k) * m⁻¹ = (m * c ^ a * m⁻¹) * (m * e ^ k * m⁻¹) := by group
    rw [h1, show m * c ^ a * m⁻¹ = (m * c * m⁻¹) ^ a from conj_zpow.symm, hmc,
      show m * e ^ k * m⁻¹ = (m * e * m⁻¹) ^ k from conj_zpow.symm, hme]
  rw [hmu]
  have hcommA : ∀ x ∈ baseA z, x * e = e * x := commute_baseA_of_commute_z hec
  have hcaA : c ^ a ∈ baseA z := (baseA z).zpow_mem hcA a
  have hc'aA : c' ^ a ∈ baseA z := (baseA z).zpow_mem hc'A a
  have hek : ∀ x ∈ baseA z, x * e ^ k = e ^ k * x := fun x hx =>
    ((show Commute x e from hcommA x hx).zpow_right k).eq
  have hcc' : c ^ a * c' ^ a = c' ^ a * c ^ a :=
    Subgroup.mul_comm_of_mem_isMulCommutative (baseA z) hcaA hc'aA
  have hcomm : (c ^ a * e ^ k) * (c' ^ a * e ^ k) = (c' ^ a * e ^ k) * (c ^ a * e ^ k) := by
    calc (c ^ a * e ^ k) * (c' ^ a * e ^ k) = c ^ a * (e ^ k * c' ^ a) * e ^ k := by group
      _ = c ^ a * (c' ^ a * e ^ k) * e ^ k := by rw [hek _ hc'aA]
      _ = (c ^ a * c' ^ a) * (e ^ k * e ^ k) := by group
      _ = (c' ^ a * c ^ a) * (e ^ k * e ^ k) := by rw [hcc']
      _ = c' ^ a * (c ^ a * e ^ k) * e ^ k := by group
      _ = c' ^ a * (e ^ k * c ^ a) * e ^ k := by rw [hek _ hcaA]
      _ = (c' ^ a * e ^ k) * (c ^ a * e ^ k) := by group
  refine ⟨hcomm.symm, ?_⟩
  intro hmem
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hCom : Commute (c ^ a) (e ^ k) := by
    show c ^ a * e ^ k = e ^ k * c ^ a
    exact (hek _ hcaA)
  have hul : (c ^ a * e ^ k) ^ l = (c ^ a) ^ l * (e ^ k) ^ l := hCom.mul_zpow l
  rw [hul] at hl
  have h2 : c' ^ a = (c ^ a) ^ l * e ^ (k * (l - 1)) := by
    have h3 : c' ^ a * e ^ k = (c ^ a) ^ l * (e ^ k) ^ l := hl.symm
    have h4 : c' ^ a = (c ^ a) ^ l * ((e ^ k) ^ l * (e ^ k)⁻¹) := by
      rw [← mul_assoc, ← h3]; group
    rw [h4]
    congr 1
    rw [← zpow_mul, ← zpow_neg, ← zpow_add]
    congr 1
    ring
  have hclA : (c ^ a) ^ l ∈ baseA z := (baseA z).zpow_mem hcaA l
  have heA' : e ^ (k * (l - 1)) ∈ baseA z := by
    have : e ^ (k * (l - 1)) = ((c ^ a) ^ l)⁻¹ * c' ^ a := by
      rw [h2]; group
    rw [this]
    exact (baseA z).mul_mem ((baseA z).inv_mem hclA) hc'aA
  have h3 := three_dvd_of_pow_mem he3 heA heA'
  have h5 := zpow_eq_one_of_dvd_three he3 h3
  rw [h5, mul_one] at h2
  apply ha3
  have hc'v : c' = vecElt z ![2, 1, 1] := by
    have hz0 : (z 0)⁻¹ = z 0 ^ 2 := by
      rw [inv_eq_iff_mul_eq_one]
      calc z 0 * z 0 ^ 2 = z 0 ^ 3 := (pow_succ' (z 0) 2).symm
        _ = 1 := hf.pow_z 0
    rw [hc']
    simp only [vecElt, hz0]
    simp [h2v, h1v]
  have hexp1 : c' ^ a = vecElt z ![(a : ZMod 3) * 2, a, a] := by
    rw [hc'v]
    have := map_zpow (vecHom hf) (Multiplicative.ofAdd (![2, 1, 1] : Fin 3 → ZMod 3)) a
    simpa [vecHom_apply, ofAdd_zsmul] using this.symm
  have hexp2 : (c ^ a) ^ l = vecElt z ![(a : ZMod 3) * l, (a : ZMod 3) * l, (a : ZMod 3) * l] := by
    rw [← zpow_mul]
    have := map_zpow (vecHom hf) (Multiplicative.ofAdd (![1, 1, 1] : Fin 3 → ZMod 3)) (a * l)
    simpa [hc, vecHom_apply, ofAdd_zsmul] using this.symm
  have hv := vecElt_injective hf (hexp1.symm.trans (h2.trans hexp2))
  have e0 : (a : ZMod 3) * 2 = (a : ZMod 3) * l := congrFun hv 0
  have e1 : (a : ZMod 3) = (a : ZMod 3) * l := congrFun hv 1
  have hz3 : ((a : ZMod 3)) = 0 := by linear_combination e0.trans e1.symm
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp hz3

theorem wreath_prod_swap {S : Type} [Group S] {z : Fin 3 → S} {t e s : S}
    (hf : WreathFacts z t) (he3 : e ^ 3 = 1) (hec : ∀ i, z i * e = e * z i)
    (heA : e ∉ baseA z) (hs : s * e * s⁻¹ = z 0) (k : ℤ) (hk3 : ¬ (3 : ℤ) ∣ k) :
    (s * e ^ k * s⁻¹) * e ^ k = e ^ k * (s * e ^ k * s⁻¹) ∧
      s * e ^ k * s⁻¹ ∉ Subgroup.zpowers (e ^ k) := by
  have hsu : s * e ^ k * s⁻¹ = z 0 ^ k := by
    rw [show s * e ^ k * s⁻¹ = (s * e * s⁻¹) ^ k from conj_zpow.symm, hs]
  rw [hsu]
  refine ⟨((show Commute (z 0) e from hec 0).zpow_zpow k k).eq, ?_⟩
  intro hmem
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hel : e ^ (k * l) ∈ baseA z := by
    rw [zpow_mul]
    rw [hl]
    exact (baseA z).zpow_mem (z_mem_baseA 0) k
  have h3 := three_dvd_of_pow_mem he3 heA hel
  have h4 : z 0 ^ k = 1 := by
    rw [← hl, ← zpow_mul, zpow_eq_one_of_dvd_three he3 h3]
  have h5 : (orderOf (z 0) : ℤ) ∣ k := orderOf_dvd_iff_zpow_eq_one.mpr h4
  rw [orderOf_z hf 0] at h5
  exact hk3 (by exact_mod_cast h5)

theorem listRow_of_wreath3_prod_gen {S : Type} [Group S] [Finite S] {z : Fin 3 → S} {t e : S}
    (hf : WreathFacts z t) (hW : Nat.card (wreathW z t) = 81) (hS : ¬ 729 ∣ Nat.card S)
    (he3 : e ^ 3 = 1) (hec : ∀ i, z i * e = e * z i) (het : t * e = e * t)
    (heW : e ∉ wreathW z t)
    (hw : ∀ a k : ℤ, ¬ ((3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ k) →
      ∃ g : S, (g * (vecElt z ![1, 1, 1] ^ a * e ^ k) * g⁻¹) * (vecElt z ![1, 1, 1] ^ a * e ^ k) =
          (vecElt z ![1, 1, 1] ^ a * e ^ k) * (g * (vecElt z ![1, 1, 1] ^ a * e ^ k) * g⁻¹) ∧
        g * (vecElt z ![1, 1, 1] ^ a * e ^ k) * g⁻¹ ∉
          Subgroup.zpowers (vecElt z ![1, 1, 1] ^ a * e ^ k)) :
    ListRow S := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWe := commute_wreathW_of_commute hec het
  set W := wreathW z t with hWdef
  have hWQ : W ≤ W ⊔ zpowers e := le_sup_left
  have hAW : baseA z ≤ wreathW z t := le_sup_left
  have heA : e ∉ baseA z := fun h => heW (hAW h)
  have hQp : IsPGroup 3 (W ⊔ zpowers e : Subgroup S) :=
    isPGroup_sup_zpowers (isPGroup_wreathW hf) he3 hWe
  obtain ⟨k5, hk5⟩ := IsPGroup.iff_card.mp hQp
  have heQ : e ∈ W ⊔ zpowers e := mem_sup_right (mem_zpowers e)
  have hne : Nat.card (W ⊔ zpowers e : Subgroup S) ≠ 81 := by
    intro h81
    have : W = W ⊔ zpowers e := Subgroup.eq_of_le_of_card_ge hWQ (by rw [h81, hW])
    exact heW (this ▸ heQ)
  have hdvd : 3 ^ k5 ∣ Nat.card S := hk5 ▸ Subgroup.card_subgroup_dvd_card _
  have h81Q : 81 ∣ Nat.card (W ⊔ zpowers e : Subgroup S) := hW ▸ Subgroup.card_dvd_of_le hWQ
  have hk5eq : k5 = 5 := by
    rw [hk5] at h81Q hne
    have h4 : 4 ≤ k5 := by
      by_contra h
      have h3k : 3 ^ k5 ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have := Nat.le_of_dvd (by positivity) h81Q
      omega
    have h5 : k5 < 6 := by
      by_contra h
      apply hS
      have := (pow_dvd_pow 3 (by omega : 6 ≤ k5)).trans hdvd
      simpa using this
    interval_cases k5
    · exact absurd (by norm_num) hne
    · rfl
  have hQcard : Nat.card (W ⊔ zpowers e : Subgroup S) = 3 ^ 5 := by rw [hk5, hk5eq]
  have hS' : ¬ 3 ^ (5 + 1) ∣ Nat.card S := by norm_num; exact hS
  haveI : IsMulCommutative (baseA z) := (isElemAbelian_baseA hf).1
  have hc3 : (vecElt z ![1, 1, 1]) ^ 3 = 1 := (isElemAbelian_baseA hf).2 _ (vecElt_mem_baseA hf _)
  refine listRow_of_sylow_center 5 (W ⊔ zpowers e) hQcard hS' fun u huQ huo hucent => ?_
  obtain ⟨w, hwW, k, hu⟩ := mem_sup_zpowers_of_commute hWe huQ
  have hwcent : ∀ q ∈ wreathW z t, q * w = w * q := by
    intro q hq
    have h1 := hucent q (hWQ hq)
    rw [hu] at h1
    have hqe : q * e ^ k = e ^ k * q := ((show Commute q e from hWe q hq).zpow_right k).eq
    have h2 : (q * w) * e ^ k = (w * q) * e ^ k := by
      calc (q * w) * e ^ k = q * (w * e ^ k) := by rw [mul_assoc]
        _ = (w * e ^ k) * q := h1
        _ = w * (e ^ k * q) := by rw [mul_assoc]
        _ = w * (q * e ^ k) := by rw [hqe]
        _ = (w * q) * e ^ k := by rw [mul_assoc]
    exact mul_right_cancel h2
  have hw_in := mem_zpowers_const_of_central hf hwW hwcent
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hw_in
  have hu' : u = vecElt z ![1, 1, 1] ^ a * e ^ k := by rw [hu, ha]
  have hnot : ¬ ((3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ k) := by
    rintro ⟨ha3, hk3⟩
    have : u = 1 := by
      rw [hu', zpow_eq_one_of_dvd_three hc3 ha3, zpow_eq_one_of_dvd_three he3 hk3, one_mul]
    rw [this, orderOf_one] at huo
    omega
  obtain ⟨g, hcomm, hn⟩ := hw a k hnot
  refine ⟨g, ?_, ?_⟩
  · rw [hu']; exact hcomm
  · rw [hu']; exact hn

theorem listRow_of_wreath3_prod {S : Type} [Group S] [Finite S] {z : Fin 3 → S} {t e m s : S}
    (hf : WreathFacts z t) (hW : Nat.card (wreathW z t) = 81) (hS : ¬ 729 ∣ Nat.card S)
    (he3 : e ^ 3 = 1) (hec : ∀ i, z i * e = e * z i) (het : t * e = e * t)
    (heW : e ∉ wreathW z t)
    (hm0 : m * z 0 * m⁻¹ = (z 0)⁻¹) (hm1 : m * z 1 * m⁻¹ = z 1) (hm2 : m * z 2 * m⁻¹ = z 2)
    (hme : m * e * m⁻¹ = e) (hs : s * e * s⁻¹ = z 0) : ListRow S := by
  have hAW : baseA z ≤ wreathW z t := le_sup_left
  have heA : e ∉ baseA z := fun h => heW (hAW h)
  refine listRow_of_wreath3_prod_gen hf hW hS he3 hec het heW fun a k hnot => ?_
  by_cases ha3 : (3 : ℤ) ∣ a
  · have hk3 : ¬ (3 : ℤ) ∣ k := fun hk => hnot ⟨ha3, hk⟩
    have hc3 : (vecElt z ![1, 1, 1]) ^ 3 = 1 :=
      (isElemAbelian_baseA hf).2 _ (vecElt_mem_baseA hf _)
    have hca : vecElt z ![1, 1, 1] ^ a = 1 := zpow_eq_one_of_dvd_three hc3 ha3
    obtain ⟨hcomm, hn⟩ := wreath_prod_swap hf he3 hec heA hs k hk3
    refine ⟨s, ?_, ?_⟩
    · rw [hca, one_mul]; exact hcomm
    · rw [hca, one_mul]; exact hn
  · exact ⟨m, wreath_prod_flip hf he3 hec heA hm0 hm1 hm2 hme a k ha3⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
