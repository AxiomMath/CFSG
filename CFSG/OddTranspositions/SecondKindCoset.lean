module

public import CFSG.OddTranspositions.SecondKindCentralizer

public section

namespace CFSG.OddTranspositions

theorem dihedral_cover {G : Type} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    {d : G} (hd : d ∈ Subgroup.closure ({a, b} : Set G)) :
    d ∈ Subgroup.zpowers (a * b) ∨ d * a ∈ Subgroup.zpowers (a * b) := by
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb_inv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hA : ∀ z : G, a * (a * z) = z := fun z => by rw [← mul_assoc, ha, one_mul]
  have hconj_mem : ∀ {y : G}, y ∈ Subgroup.zpowers (a * b) →
      a * y * a ∈ Subgroup.zpowers (a * b) := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have ha_mul : a * (a * b) * a = (a * b)⁻¹ := by
      rw [mul_inv_rev, ha_inv, hb_inv, ← mul_assoc, ha, one_mul]
    have e : a * (a * b) ^ k * a = ((a * b)⁻¹) ^ k := by
      rw [← ha_mul]
      have := map_zpow (MulAut.conj a) (a * b) k
      simpa [MulAut.conj_apply, ha_inv] using this
    rw [e]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) k
  induction hd using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · right; rw [ha]; exact Subgroup.one_mem _
    · right
      have : x * a = (a * x)⁻¹ := by rw [mul_inv_rev, ha_inv, hb_inv]
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  | one => left; exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
    rcases ihx with hx' | hx' <;> rcases ihy with hy' | hy'
    · left; exact Subgroup.mul_mem _ hx' hy'
    · right
      have : x * y * a = x * (y * a) := by rw [mul_assoc]
      rw [this]; exact Subgroup.mul_mem _ hx' hy'
    · right
      have : x * y * a = (x * a) * (a * y * a) := by
        simp only [mul_assoc, hA]
      rw [this]; exact Subgroup.mul_mem _ hx' (hconj_mem hy')
    · left
      have : x * y = (x * a) * (a * (y * a) * a) := by
        simp only [mul_assoc, hA, ha, mul_one]
      rw [this]; exact Subgroup.mul_mem _ hx' (hconj_mem hy')
  | inv x hx ihx =>
    rcases ihx with hx' | hx'
    · left; exact Subgroup.inv_mem _ hx'
    · right
      have : x⁻¹ * a = a * (x * a)⁻¹ * a := by
        simp only [mul_inv_rev, ha_inv, hA]
      rw [this]; exact hconj_mem (Subgroup.inv_mem _ hx')

theorem dihedral_centralizer_involution {G : Type} [Group G] {u w d : G}
    (hu : u * u = 1) (hw : w * w = 1) (hodd : Odd (orderOf (u * w)))
    (hd : d ∈ Subgroup.closure ({u, w} : Set G)) (hd2 : d * d = 1)
    (hdc : Commute d u) :
    d ∈ Subgroup.zpowers u := by
  have key : ∀ x : G, x ∈ Subgroup.zpowers (u * w) → x * x = 1 → x = 1 := by
    intro x hx hx2
    have hdvd : orderOf x ∣ orderOf (u * w) := orderOf_dvd_of_mem_zpowers hx
    have h2 : orderOf x ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hx2)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact absurd h (hodd.ne_two_of_dvd_nat hdvd)
  rcases dihedral_cover hu hw hd with hrot | href
  · rw [key d hrot hd2]
    exact Subgroup.one_mem _
  ·
    have hdu2 : (d * u) * (d * u) = 1 := by
      calc (d * u) * (d * u) = d * (u * (d * u)) := by rw [mul_assoc]
        _ = d * ((u * d) * u) := by rw [mul_assoc]
        _ = d * ((d * u) * u) := by rw [← hdc.eq]
        _ = d * (d * (u * u)) := by rw [mul_assoc]
        _ = 1 := by rw [hu, mul_one, hd2]
    have h1 : d * u = 1 := key (d * u) href hdu2
    have hdu : d = u := by
      calc d = d * 1 := (mul_one d).symm
        _ = d * (u * u) := by rw [hu]
        _ = (d * u) * u := by rw [mul_assoc]
        _ = 1 * u := by rw [h1]
        _ = u := one_mul u
    rw [hdu]
    exact Subgroup.mem_zpowers u

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity
open scoped commutatorElement
open CFSG.Timmesfeld.Bridge.OddTransp

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem secondKind_mem_sup_Q (hD : IsOddTransp D) (hN : IsNormalSet D)
    {u w v d : G} (htri : IsTriangle D u w v) (h4 : orderOf (u * v * w) = 4)
    (hno : ∀ x ∈ D, x ∈ Subgroup.closure {u, w} → IsTriangle D u x v →
      ¬ IsThirdKind u x v)
    (hd : d ∈ D) (hdK : d ∈ Subgroup.closure {u, w, v}) (hdu : Commute d u) :
    d ∈ Subgroup.zpowers u ⊔ conjClosure (Subgroup.closure {u, w}) (u * v) := by
  classical
  let X : Subgroup G := Subgroup.closure ({u, w} : Set G)
  let Q : Subgroup G := conjClosure X (u * v)
  let K : Subgroup G := Subgroup.closure ({u, w, v} : Set G)
  have hS : SecondKindStructure u w v := secondKind_structure hD hN htri h4 hno
  have hK : X ⊔ Q = K := secondKind_closure_eq hD hN htri h4 hno
  have hXK : X ≤ K := by
    intro x hx
    exact Subgroup.closure_mono (by intro y hy; rcases hy with rfl | rfl <;> simp) hx
  have hQK : Q ≤ K := hS.le
  let QK : Subgroup ↥K := Q.subgroupOf K
  haveI hQKnormal : QK.Normal :=
    (Subgroup.normal_subgroupOf_iff hQK).mpr fun h k hh hk => hS.normal k hk h hh
  let π : ↥K →* ↥K ⧸ QK := QuotientGroup.mk' QK
  have huK : u ∈ K := Subgroup.subset_closure (by simp)
  have hwK : w ∈ K := Subgroup.subset_closure (by simp)
  have hXK_eq : Subgroup.closure ({⟨u, huK⟩, ⟨w, hwK⟩} : Set ↥K) = X.subgroupOf K := by
    apply Subgroup.map_injective K.subtype_injective
    rw [MonoidHom.map_closure, Subgroup.map_subgroupOf_eq_of_le hXK]
    congr 1
    ext g
    simp
  have hsupXQ : X.subgroupOf K ⊔ QK = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (B := K) hXK hQK, hK, Subgroup.subgroupOf_self]
  have hmap_top : (X.subgroupOf K ⊔ QK).map π = ⊤ := by
    rw [hsupXQ, Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective QK)]
  have hmapX : (X.subgroupOf K).map π = ⊤ := by
    have := hmap_top
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] at this
  let a : ↥K ⧸ QK := π ⟨u, huK⟩
  let b : ↥K ⧸ QK := π ⟨w, hwK⟩
  have hgen : Subgroup.closure ({a, b} : Set (↥K ⧸ QK)) = ⊤ := by
    rw [← hmapX, ← hXK_eq, MonoidHom.map_closure]
    congr 1
    ext y
    simp [a, b]
  have ha2 : a * a = 1 := by
    have h1 : (⟨u, huK⟩ : ↥K) * ⟨u, huK⟩ = 1 := by
      ext
      simpa using hD.mul_self_eq_one htri.1
    change π ⟨u, huK⟩ * π ⟨u, huK⟩ = 1
    rw [← map_mul, h1, map_one]
  have hb2 : b * b = 1 := by
    have h1 : (⟨w, hwK⟩ : ↥K) * ⟨w, hwK⟩ = 1 := by
      ext
      simpa using hD.mul_self_eq_one htri.2.2.1
    change π ⟨w, hwK⟩ * π ⟨w, hwK⟩ = 1
    rw [← map_mul, h1, map_one]
  have hodd : Odd (orderOf (a * b)) := by
    have hdvd : orderOf (a * b) ∣ orderOf ((⟨u, huK⟩ : ↥K) * ⟨w, hwK⟩) := by
      have hprod : a * b = π ((⟨u, huK⟩ : ↥K) * ⟨w, hwK⟩) := by
        change π ⟨u, huK⟩ * π ⟨w, hwK⟩ = π (⟨u, huK⟩ * ⟨w, hwK⟩)
        rw [map_mul]
      rw [hprod]
      exact orderOf_map_dvd π _
    have hord : orderOf ((⟨u, huK⟩ : ↥K) * ⟨w, hwK⟩) = orderOf (u * w) := by
      simpa using Subgroup.orderOf_mk (G := G) (H := K) (u * w) (K.mul_mem huK hwK)
    have huw : Odd (orderOf (u * w)) :=
      hD.odd_of_not_commute htri.1 htri.2.2.1 htri.2.2.2.2.2.1
    rw [hord] at hdvd
    exact huw.of_dvd_nat hdvd
  let z : ↥K ⧸ QK := π ⟨d, hdK⟩
  have hz2 : z * z = 1 := by
    have h1 : (⟨d, hdK⟩ : ↥K) * ⟨d, hdK⟩ = 1 := by
      ext
      simpa using hD.mul_self_eq_one hd
    change π ⟨d, hdK⟩ * π ⟨d, hdK⟩ = 1
    rw [← map_mul, h1, map_one]
  have hza : Commute z a := by
    have hduK : Commute (⟨d, hdK⟩ : ↥K) ⟨u, huK⟩ := by
      show (⟨d, hdK⟩ : ↥K) * ⟨u, huK⟩ = ⟨u, huK⟩ * ⟨d, hdK⟩
      ext
      exact hdu.eq
    simpa [z, a] using hduK.map π
  have hzcl : z ∈ Subgroup.closure ({a, b} : Set (↥K ⧸ QK)) := by
    rw [hgen]
    exact Subgroup.mem_top z
  have hzpow : z ∈ Subgroup.zpowers a :=
    dihedral_centralizer_involution ha2 hb2 hodd hzcl hz2 hza
  have hzmap : (Subgroup.zpowers (⟨u, huK⟩ : ↥K)).map π = Subgroup.zpowers a :=
    MonoidHom.map_zpowers π ⟨u, huK⟩
  have hzpow' : z ∈ (Subgroup.zpowers (⟨u, huK⟩ : ↥K)).map π := by
    rwa [hzmap]
  obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hzpow'
  have hker : x⁻¹ * ⟨d, hdK⟩ ∈ (QuotientGroup.mk' QK).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxeq]
    change z⁻¹ * z = 1
    exact inv_mul_cancel z
  have hmemQK : x⁻¹ * ⟨d, hdK⟩ ∈ QK := by
    rw [← QuotientGroup.ker_mk' QK]
    exact hker
  have hmemQ : (((x⁻¹ * ⟨d, hdK⟩ : ↥K) : G)) ∈ Q :=
    Subgroup.mem_subgroupOf.mp hmemQK
  have hxval : ((x : ↥K) : G) ∈ Subgroup.zpowers u := by
    have hxmap := Subgroup.mem_map_of_mem (f := K.subtype) hx
    rw [MonoidHom.map_zpowers] at hxmap
    simpa using hxmap
  have hd_eq : d = ((x : ↥K) : G) * (((x⁻¹ * ⟨d, hdK⟩ : ↥K) : G)) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
    group
  rw [hd_eq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hxval) (Subgroup.mem_sup_right hmemQ)

open scoped commutatorElement

theorem conj_eq_mul_commutator {G : Type} [Group G] {u q : G}
    (hu : u * u = 1) (hq : q * q = 1) :
    q * u * q⁻¹ = u * ⁅u, q⁆ := by
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hq' : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq
  rw [commutatorElement_def, hu', hq']
  rw [show u * (u * q * u * q) = (u * u) * (q * u * q) by group, hu, one_mul]

theorem isPGroup_sup_zpowers_Q (hD : IsOddTransp D) (hN : IsNormalSet D)
    {u w v : G} (htri : IsTriangle D u w v) (h4 : orderOf (u * v * w) = 4)
    (hno : ∀ x ∈ D, x ∈ Subgroup.closure {u, w} → IsTriangle D u x v →
      ¬ IsThirdKind u x v) :
    IsPGroup 2 ↥(Subgroup.zpowers u ⊔ conjClosure (Subgroup.closure {u, w}) (u * v)) := by
  classical
  let X : Subgroup G := Subgroup.closure ({u, w} : Set G)
  let Q : Subgroup G := conjClosure X (u * v)
  let K : Subgroup G := Subgroup.closure ({u, w, v} : Set G)
  have hS : SecondKindStructure u w v := secondKind_structure hD hN htri h4 hno
  have huK : u ∈ K := Subgroup.subset_closure (by simp)
  have hQK : Q ≤ K := hS.le
  let QK : Subgroup ↥K := Q.subgroupOf K
  haveI hQKnormal : QK.Normal :=
    (Subgroup.normal_subgroupOf_iff hQK).mpr fun h k hh hk => hS.normal k hk h hh
  let UK : Subgroup ↥K := Subgroup.zpowers (⟨u, huK⟩ : K)
  have hUK2 : (⟨u, huK⟩ : K) * ⟨u, huK⟩ = 1 := by
    ext
    simpa using hD.mul_self_eq_one htri.1
  have hUKp : IsPGroup 2 UK := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one]
    have hdvd : orderOf (x : ↥K) ∣ orderOf (⟨u, huK⟩ : K) :=
      orderOf_dvd_of_mem_zpowers x.2
    have h2 : orderOf (⟨u, huK⟩ : K) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (n := 2) (by simpa [pow_two] using hUK2)
    rw [← Subgroup.orderOf_coe x]
    exact hdvd.trans h2
  have hQKp : IsPGroup 2 QK := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one]
    have hx2 : (x : ↥K) * (x : ↥K) = 1 := by
      ext
      simpa using hS.sq (((x : ↥K) : G)) (Subgroup.mem_subgroupOf.mp x.2)
    have hdvd : orderOf (x : ↥K) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (n := 2) (by simpa [pow_two] using hx2)
    rw [← Subgroup.orderOf_coe x]
    exact hdvd
  have hsupP : IsPGroup 2 ↥(UK ⊔ QK) := IsPGroup.to_sup_of_normal_right hUKp hQKp
  have hmap : (UK ⊔ QK).map K.subtype = Subgroup.zpowers u ⊔ Q := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.map_subgroupOf_eq_of_le hQK]
    rfl
  exact hmap ▸ hsupP.map K.subtype

theorem commute_of_mem_sup_D (hD : IsOddTransp D) (hN : IsNormalSet D)
    {u w v d e : G} (htri : IsTriangle D u w v) (h4 : orderOf (u * v * w) = 4)
    (hno : ∀ x ∈ D, x ∈ Subgroup.closure {u, w} → IsTriangle D u x v →
      ¬ IsThirdKind u x v)
    (hd : d ∈ D) (he : e ∈ D)
    (hdS : d ∈ Subgroup.zpowers u ⊔ conjClosure (Subgroup.closure {u, w}) (u * v))
    (heS : e ∈ Subgroup.zpowers u ⊔ conjClosure (Subgroup.closure {u, w}) (u * v)) :
    Commute d e :=
  hD.commute_of_isPGroup (isPGroup_sup_zpowers_Q hD hN htri h4 hno) hd he hdS heS

theorem orbit_u_spec (hD : IsOddTransp D) (hN : IsNormalSet D)
    {u w v : G} (htri : IsTriangle D u w v) (h4 : orderOf (u * v * w) = 4)
    (hno : ∀ x ∈ D, x ∈ Subgroup.closure {u, w} → IsTriangle D u x v →
      ¬ IsThirdKind u x v)
    {q : G} (hq : q ∈ conjClosure (Subgroup.closure {u, w}) (u * v)) :
    q * u * q⁻¹ ∈ D ∧ q * u * q⁻¹ ∈ Subgroup.closure {u, w, v} ∧
      Commute (q * u * q⁻¹) u := by
  have S : SecondKindStructure u w v :=
    CFSG.Timmesfeld.Bridge.OddTransp.secondKind_structure hD hN htri h4 hno
  have huK : u ∈ Subgroup.closure ({u, w, v} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hqK : q ∈ Subgroup.closure ({u, w, v} : Set G) := by
    rw [← secondKind_closure_eq hD hN htri h4 hno]
    exact Subgroup.mem_sup_right hq
  have hq2 : q * q = 1 := S.sq q hq
  have hu2 : u * u = 1 := hD.mul_self_eq_one htri.1
  refine ⟨hN q u htri.1, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hqK huK) (Subgroup.inv_mem _ hqK)
  · rw [conj_eq_mul_commutator hu2 hq2]
    have hc : Commute ⁅u, q⁆ u := by
      have hmem : ⁅u, q⁆ ∈ ⁅conjClosure (Subgroup.closure {u, w}) (u * v),
          Subgroup.zpowers u⁆ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator
          (Subgroup.mem_zpowers u) hq
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (secondKind_commutator_le_centralizer hD hN htri h4 hno hmem)
    exact (Commute.refl u).mul_left hc

theorem mul_commutator_mem_D_inter_S (hD : IsOddTransp D) (hN : IsNormalSet D)
    {u w v : G} (htri : IsTriangle D u w v) (h4 : orderOf (u * v * w) = 4)
    (hno : ∀ x ∈ D, x ∈ Subgroup.closure {u, w} → IsTriangle D u x v →
      ¬ IsThirdKind u x v)
    {q : G} (hq : q ∈ conjClosure (Subgroup.closure {u, w}) (u * v)) :
    u * ⁅u, q⁆ ∈ D ∧
      u * ⁅u, q⁆ ∈ Subgroup.zpowers u ⊔ conjClosure (Subgroup.closure {u, w}) (u * v) := by
  have S : SecondKindStructure u w v :=
    CFSG.Timmesfeld.Bridge.OddTransp.secondKind_structure hD hN htri h4 hno
  have hq2 : q * q = 1 := S.sq q hq
  have hu2 : u * u = 1 := hD.mul_self_eq_one htri.1
  have hspec := orbit_u_spec hD hN htri h4 hno (q := q) hq
  have heq : u * ⁅u, q⁆ = q * u * q⁻¹ := (conj_eq_mul_commutator hu2 hq2).symm
  constructor
  · rw [heq]; exact hspec.1
  · rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mem_sup_right hq) (Subgroup.mem_sup_left (Subgroup.mem_zpowers u)))
      (Subgroup.inv_mem _ (Subgroup.mem_sup_right hq))

end CFSG.OddTranspositions
