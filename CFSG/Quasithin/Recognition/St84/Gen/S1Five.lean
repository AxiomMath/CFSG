module

public import CFSG.GH74.QTGen4.DSGen4.Defs
public import CFSG.GH74.QTGen4.DSGen4.Statements

public section

namespace CFSG.Quasithin.St84

open CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem elementary_of_sq_const {H : Type*} [Group H] (V : Subgroup H)
    (hVc : ∀ v ∈ V, ∀ g : H, g * v = v * g) (hV2 : ∀ v ∈ V, v ^ 2 = 1)
    (a b d c : H) (ha : a ∉ V) (hb : b ∉ V) (hd : d ∉ V) (hab : a * b ∉ V)
    (had : a * d ∉ V) (hbd : b * d ∉ V) (habd : a * (b * d) ∉ V)
    (hcV : c ∈ V) (hconst : ∀ x : H, x ∉ V → x ^ 2 = c) :
    ∀ x : H, x ^ 2 = 1 ∧ ∀ y : H, x * y = y * x := by
  have hc2 : c ^ 2 = 1 := hV2 c hcV
  have hcc : ∀ g : H, g * c = c * g := fun g => hVc c hcV g
  have hcomm : ∀ y : H, y ∉ V → a * y ∉ V → a * y * a⁻¹ * y⁻¹ = c := by
    intro y hy hay
    have h1 := CFSG.GH74.KGroups.comm_eq_sq a y c (a * y * a⁻¹ * y⁻¹)
      (hconst a ha) (hconst y hy) hcc hc2 rfl
    exact h1.symm.trans (hconst (a * y) hay)
  have e1 := hcomm b hb hab
  have e2 := hcomm d hd had
  have e3 := hcomm (b * d) hbd habd
  have hid : a * (b * d) * a⁻¹ * (b * d)⁻¹ =
      (a * b * a⁻¹ * b⁻¹) * (b * (a * d * a⁻¹ * d⁻¹) * b⁻¹) := by group
  rw [e1, e2, e3, hcc b] at hid
  rw [mul_inv_cancel_right] at hid
  have hc1 : c = 1 := by
    rw [show c * c = 1 by rw [← pow_two]; exact hc2] at hid
    exact hid
  have hall : ∀ x : H, x ^ 2 = 1 := by
    intro x
    by_cases hx : x ∈ V
    · exact hV2 x hx
    · rw [hconst x hx, hc1]
  refine fun x => ⟨hall x, fun y => ?_⟩
  have hinv : ∀ z : H, z⁻¹ = z := fun z =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hall z)
  have h1 : (x * y)⁻¹ = x * y := hinv (x * y)
  rw [mul_inv_rev, hinv x, hinv y] at h1
  exact h1.symm

theorem isElemSec_of_transitive {K A Q L : Subgroup G} (hQL : Q ≤ L) (hA : IsElemSec K A)
    (hQ : IsElemSec A Q) (hcen : ∀ a ∈ A, ∀ l ∈ L, ⁅a, l⁆ ∈ K) (hcard : 8 ≤ A.relIndex Q)
    (htrans : ∀ x ∈ Q, x ∉ A → ∀ y ∈ Q, y ∉ A → ∃ l ∈ L, y⁻¹ * (l * x * l⁻¹) ∈ A) :
    IsElemSec K Q := by
  classical
  have hKA : K ≤ A := hA.1
  have hAQ : A ≤ Q := hQ.1
  have hKQ : K ≤ Q := hKA.trans hAQ
  have hsqQ : ∀ x ∈ Q, x ^ 2 ∈ A := hQ.2.2
  have hsqA : ∀ a ∈ A, a ^ 2 ∈ K := hA.2.2
  have hKconj : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K := by
    intro l hl k hk
    have hc : ⁅k⁻¹, l⁆ ∈ K := hcen k⁻¹ (hKA (K.inv_mem hk)) l hl
    have e : l * k * l⁻¹ = k * ⁅k⁻¹, l⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact K.mul_mem hk hc
  have hsq_conj : ∀ l ∈ L, ∀ x ∈ Q, (l * x * l⁻¹) ^ 2 * (x ^ 2)⁻¹ ∈ K := by
    intro l hl x hx
    have hc : ⁅x ^ 2, l⁆ ∈ K := hcen (x ^ 2) (hsqQ x hx) l hl
    have e : (l * x * l⁻¹) ^ 2 * (x ^ 2)⁻¹ = ⁅l, x ^ 2⁆ := by
      have e1 : (l * x * l⁻¹) ^ 2 = l * x ^ 2 * l⁻¹ := by
        rw [pow_two, pow_two]
        group
      rw [e1]
      simp only [commutatorElement_def]
    rw [e, ← commutatorElement_inv]
    exact K.inv_mem hc
  have hsq_mul : ∀ x ∈ Q, ∀ a ∈ A, (x * a) ^ 2 * (x ^ 2)⁻¹ ∈ K := by
    intro x hx a ha
    have hxL : x ∈ L := hQL hx
    have hcx : ⁅x⁻¹, a⁆ ∈ K := by
      have hc : ⁅a, x⁆ ∈ K := hcen a ha x hxL
      have e : ⁅x⁻¹, a⁆ = x⁻¹ * ⁅a, x⁆ * x := by
        simp only [commutatorElement_def]
        group
      rw [e]
      simpa only [inv_inv] using hKconj x⁻¹ (L.inv_mem hxL) ⁅a, x⁆ hc
    have e : (x * a) ^ 2 = x ^ 2 * (⁅x⁻¹, a⁆ * a ^ 2) := by
      rw [pow_two]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hKconj (x ^ 2) (hQL (Q.pow_mem hx 2)) (⁅x⁻¹, a⁆ * a ^ 2)
      (K.mul_mem hcx (hsqA a ha))
  have hcardQ : 8 ≤ (A.subgroupOf Q).index := by
    simpa only [Subgroup.relIndex] using hcard
  have hex : ∃ q : ↥Q, q ∉ A.subgroupOf Q := by
    by_contra h
    have htop : A.subgroupOf Q = ⊤ := top_unique fun q _ => by
      by_contra hq
      exact h ⟨q, hq⟩
    have h1 := hcardQ
    rw [htop, Subgroup.index_top] at h1
    omega
  obtain ⟨q0, hq0⟩ := hex
  have hq0A : (q0 : G) ∉ A := fun h => hq0 (Subgroup.mem_subgroupOf.mpr h)
  have hq0Q : (q0 : G) ∈ Q := q0.2
  have hsame : ∀ x ∈ Q, x ∉ A → x ^ 2 * ((q0 : G) ^ 2)⁻¹ ∈ K := by
    intro x hxQ hxA
    obtain ⟨l, hlL, hl⟩ := htrans q0 hq0Q hq0A x hxQ hxA
    set t : G := x⁻¹ * (l * (q0 : G) * l⁻¹) with htdef
    have htA : t ∈ A := hl
    have hxt : l * (q0 : G) * l⁻¹ = x * t := by
      rw [htdef]
      group
    have h1 : (x * t) ^ 2 * ((q0 : G) ^ 2)⁻¹ ∈ K := by
      have h := hsq_conj l hlL (q0 : G) hq0Q
      rwa [hxt] at h
    have h2 : (x * t) ^ 2 * (x ^ 2)⁻¹ ∈ K := hsq_mul x hxQ t htA
    have e : x ^ 2 * ((q0 : G) ^ 2)⁻¹ =
        (x ^ 2 * ((x * t) ^ 2)⁻¹) * ((x * t) ^ 2 * ((q0 : G) ^ 2)⁻¹) := by
      group
    have h2' : x ^ 2 * ((x * t) ^ 2)⁻¹ ∈ K := by
      simpa only [mul_inv_rev, inv_inv] using K.inv_mem h2
    rw [e]
    exact K.mul_mem h2' h1
  let N : Subgroup ↥Q := K.subgroupOf Q
  haveI hNnormal : N.Normal :=
    (Subgroup.normal_subgroupOf_iff hKQ).mpr fun k q hk hq => hKconj q (hQL hq) k hk
  let H := ↥Q ⧸ N
  let f : ↥Q →* H := QuotientGroup.mk' N
  let V : Subgroup H := (A.subgroupOf Q).map f
  have hVc : ∀ v ∈ V, ∀ g : H, g * v = v * g := by
    intro v hv g
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hv
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective N g
    have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
    have hqQ : (q : G) ∈ Q := q.2
    change ((q * a : ↥Q) : H) = ((a * q : ↥Q) : H)
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    have hc : ⁅(q : G), (a : G)⁆ ∈ K := by
      rw [← commutatorElement_inv]
      exact K.inv_mem (hcen (a : G) haA (q : G) (hQL hqQ))
    have e : (((q * a) / (a * q) : ↥Q) : G) = ⁅(q : G), (a : G)⁆ := by
      simp only [div_eq_mul_inv, mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.coe_zpow, commutatorElement_def]
      group
    rw [e]
    exact hc
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hv
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (a ^ 2)).mpr
      (Subgroup.mem_subgroupOf.mpr (hsqA (a : G) (Subgroup.mem_subgroupOf.mp ha)))
  have hVindex : V.index = (A.subgroupOf Q).index := by
    change ((A.subgroupOf Q).map f).index = (A.subgroupOf Q).index
    exact Subgroup.index_map_eq (H := A.subgroupOf Q) (f := f)
      (QuotientGroup.mk'_surjective N) (by
      change (QuotientGroup.mk' N).ker ≤ A.subgroupOf Q
      rw [QuotientGroup.ker_mk']
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hKA (Subgroup.mem_subgroupOf.mp hx)))
  have hV8 : 8 ≤ V.index := by
    rw [hVindex]
    exact hcardQ
  have hVnormal : V.Normal :=
    Subgroup.normal_of_le_center fun v hv => Subgroup.mem_center_iff.mpr (hVc v hv)
  have hconst : ∃ c ∈ V, ∀ x : H, x ∉ V → x ^ 2 = c := by
    refine ⟨f (q0 ^ 2), Subgroup.mem_map.mpr ⟨q0 ^ 2, ?_, rfl⟩, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr (hsqQ (q0 : G) hq0Q)
    · intro x hx
      obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective N x
      have hqA : (q : G) ∉ A := fun h =>
        hx (Subgroup.mem_map.mpr ⟨q, Subgroup.mem_subgroupOf.mpr h, rfl⟩)
      have hk : (q : G) ^ 2 * ((q0 : G) ^ 2)⁻¹ ∈ K := hsame (q : G) q.2 hqA
      have hN : (q ^ 2) / (q0 ^ 2) ∈ N := by
        rw [Subgroup.mem_subgroupOf]
        simpa only [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv]
          using hk
      have hf : f (q ^ 2) = f (q0 ^ 2) :=
        (QuotientGroup.eq_iff_div_mem (x := q ^ 2) (y := q0 ^ 2)).mpr hN
      rw [← map_pow, hf]
  have hsqV : ∀ h : H, h ^ 2 ∈ V := by
    intro h
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective N h
    rw [← map_pow]
    exact Subgroup.mem_map.mpr
      ⟨q ^ 2, Subgroup.mem_subgroupOf.mpr (hsqQ (q : G) q.2), rfl⟩
  haveI : V.Normal := hVnormal
  have hGqcard : 8 ≤ Nat.card (H ⧸ V) := by
    rw [← Subgroup.index_eq_card]
    exact hV8
  have hGq2 : ∀ z : H ⧸ V, z ^ 2 = 1 := by
    intro z
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective V z
    rw [← map_pow]
    change ((h ^ 2 : H) : H ⧸ V) = 1
    rw [QuotientGroup.eq_one_iff]
    exact hsqV h
  obtain ⟨abar, -, habar⟩ := CFSG.GH74.KGroups.exists_mem_notMem_list
    (⊤ : Subgroup (H ⧸ V)) [1] (by simpa using (show 1 < Nat.card (H ⧸ V) by omega))
  obtain ⟨bbar, -, hbbar⟩ := CFSG.GH74.KGroups.exists_mem_notMem_list
    (⊤ : Subgroup (H ⧸ V)) [1, abar] (by simpa using (show 2 < Nat.card (H ⧸ V) by omega))
  obtain ⟨dbar, -, hdbar⟩ := CFSG.GH74.KGroups.exists_mem_notMem_list
    (⊤ : Subgroup (H ⧸ V)) [1, abar, bbar, abar * bbar]
    (by simpa using (show 4 < Nat.card (H ⧸ V) by omega))
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at habar hbbar hdbar
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective V abar
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective V bbar
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective V dbar
  have hmul_ne : ∀ z w : H ⧸ V, z ≠ w → w ^ 2 = 1 → z * w ≠ 1 := by
    intro z w hzw hw h
    apply hzw
    calc z = z * (w * w) := by
          rw [show w * w = 1 by rw [← pow_two]; exact hw, mul_one]
      _ = (z * w) * w := by group
      _ = w := by rw [h, one_mul]
  have haV : a ∉ V := fun h => habar ((QuotientGroup.eq_one_iff a).mpr h)
  have hbV : b ∉ V := fun h => hbbar.1 ((QuotientGroup.eq_one_iff b).mpr h)
  have hdV : d ∉ V := fun h => hdbar.1 ((QuotientGroup.eq_one_iff d).mpr h)
  have habV : a * b ∉ V := by
    intro h
    have h1 : (a : H ⧸ V) * (b : H ⧸ V) = 1 := by
      simpa using (QuotientGroup.eq_one_iff (a * b)).mpr h
    exact hmul_ne (a : H ⧸ V) (b : H ⧸ V) (Ne.symm hbbar.2) (hGq2 b) h1
  have hadV : a * d ∉ V := by
    intro h
    have h1 : (a : H ⧸ V) * (d : H ⧸ V) = 1 := by
      simpa using (QuotientGroup.eq_one_iff (a * d)).mpr h
    exact hmul_ne (a : H ⧸ V) (d : H ⧸ V) (Ne.symm hdbar.2.1) (hGq2 d) h1
  have hbdV : b * d ∉ V := by
    intro h
    have h1 : (b : H ⧸ V) * (d : H ⧸ V) = 1 := by
      simpa using (QuotientGroup.eq_one_iff (b * d)).mpr h
    exact hmul_ne (b : H ⧸ V) (d : H ⧸ V) (Ne.symm hdbar.2.2.1) (hGq2 d) h1
  have habdV : a * (b * d) ∉ V := by
    intro h
    have h1 : ((a * (b * d) : H) : H ⧸ V) = 1 :=
      (QuotientGroup.eq_one_iff (a * (b * d))).mpr h
    have h2 : ((a : H ⧸ V) * (b : H ⧸ V)) * (d : H ⧸ V) = 1 := by
      simpa only [QuotientGroup.mk_mul, mul_assoc] using h1
    exact hmul_ne ((a : H ⧸ V) * (b : H ⧸ V)) (d : H ⧸ V)
      (Ne.symm hdbar.2.2.2) (hGq2 d) h2
  obtain ⟨c, hcV, hconst'⟩ := hconst
  have hH := elementary_of_sq_const V hVc hV2 a b d c haV hbV hdV habV hadV hbdV habdV
    hcV hconst'
  refine ⟨hKQ, ?_, ?_⟩
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    let qx : ↥Q := ⟨x, hx⟩
    let qy : ↥Q := ⟨y, hy⟩
    have hxy : f qx * f qy = f qy * f qx := (hH (f qx)).2 (f qy)
    have hxy' : (qx * qy : H) = (qy * qx : H) := by
      change f (qx * qy) = f (qy * qx)
      simpa only [map_mul] using hxy
    have hNmem : (qx * qy) / (qy * qx) ∈ N :=
      (QuotientGroup.eq_iff_div_mem).mp hxy'
    have hKmem : (((qx * qy) / (qy * qx) : ↥Q) : G) ∈ K :=
      Subgroup.mem_subgroupOf.mp hNmem
    have e : ⁅x, y⁆ = (((qx * qy) / (qy * qx) : ↥Q) : G) := by
      simp only [qx, qy, div_eq_mul_inv, mul_inv_rev, Subgroup.coe_mul,
        Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    exact hKmem
  · intro x hx
    let qx : ↥Q := ⟨x, hx⟩
    have h2 : f qx ^ 2 = 1 := (hH (f qx)).1
    have hNmem : qx ^ 2 ∈ N :=
      (QuotientGroup.eq_one_iff (qx ^ 2)).mp (by
        change f (qx ^ 2) = 1
        simpa only [map_pow] using h2)
    have hKmem : ((qx ^ 2 : ↥Q) : G) ∈ K := Subgroup.mem_subgroupOf.mp hNmem
    simpa only [qx, Subgroup.coe_pow] using hKmem

end CFSG.Quasithin.St84
