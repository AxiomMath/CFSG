module

public import CFSG.OddTranspositions.PartThree.EightFive.QNotCentralCoreBasic
import CFSG.Timmesfeld.Bridge.Asc72YWidth
import CFSG.OddTranspositions.SixSeven
import CFSG.GroupTheory.PCore.InfPCoreOf
public import CFSG.Timmesfeld.Bridge.Asc72XEnd

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddTransp

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_sylow_of_thirdKind_conj (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n)
    (hord : orderOf (u * v * w) = 2 * n) {z : G} (hzdef : (u * v * w) ^ n = z)
    {q : localGroup D z} (hq : q ∈ CFSG.pCore 2 (localGroup D z)) {a : G}
    (hadef : (q : G) * u * (q : G)⁻¹ = a) :
    ∃ S₀ : Sylow 2 G, u ∈ S₀ ∧ v ∈ S₀ ∧ u * v * z ∈ S₀ ∧ a ∈ D ∩ (S₀ : Set G) ∧
      (CFSG.pCore 2 (localGroup D z)).map (localGroup D z).subtype ≤ S₀ := by
  have hD := hS.oddT
  obtain ⟨-, hz1, hzu, hzv, hzw, hbD⟩ := htri.third_kind hD hS.normal hn hord
  obtain ⟨huC, hvC, hwC, hdC⟩ := thirdKind_mem_centSet hS htri hn hord
  rw [hzdef] at hzu hzv hzw hbD huC hvC hwC hdC
  have hu : u ∈ D := htri.1
  have hv : v ∈ D := htri.2.1
  have hne : u ≠ v := htri.2.2.2.1
  have huv : Commute u v := htri.2.2.2.2.1
  have hbu : Commute (u * v * z) u := by
    have h1 : Commute (u * v * z) (u * v) :=
      (Commute.refl (u * v)).mul_left (hzu.mul_right hzv)
    exact (hD.commute_mul_iff hu hv hbD hne huv).mp h1 |>.1
  have hbv : Commute (u * v * z) v := by
    have h1 : Commute (u * v * z) (u * v) :=
      (Commute.refl (u * v)).mul_left (hzu.mul_right hzv)
    exact (hD.commute_mul_iff hu hv hbD hne huv).mp h1 |>.2
  obtain ⟨S₀, huS, hvS, hbS, hQS⟩ :=
    exists_sylow_localGroup hD huC hvC hdC huv hbu.symm hbv.symm
  have haD : a ∈ D := by
    rw [← hadef]
    exact hS.conj_mem (q : G) hu
  have hqS : (q : G) ∈ S₀ := hQS ⟨q, hq, rfl⟩
  have haS : a ∈ S₀ := by
    rw [← hadef]
    exact S₀.mul_mem (S₀.mul_mem hqS huS) (S₀.inv_mem hqS)
  exact ⟨S₀, huS, hvS, hbS, ⟨haD, haS⟩, hQS⟩

omit [Finite G] in
theorem conj_mul_inv_mem_pCore {z u a : G} (hu : u ∈ localGroup D z)
    {q : localGroup D z} (hq : q ∈ CFSG.pCore 2 (localGroup D z))
    (hadef : (q : G) * u * (q : G)⁻¹ = a) :
    a * u⁻¹ ∈ (CFSG.pCore 2 (localGroup D z)).map (localGroup D z).subtype := by
  have hconj : (⟨u, hu⟩ : localGroup D z) * q * (⟨u, hu⟩ : localGroup D z)⁻¹ ∈
      CFSG.pCore 2 (localGroup D z) :=
    (CFSG.pCore_normal (p := 2) (G := localGroup D z)).conj_mem q hq ⟨u, hu⟩
  have h : a * u⁻¹ = (q : G) * (u * (q : G) * u⁻¹)⁻¹ := by
    rw [← hadef]
    group
  refine Subgroup.mem_map.mpr ⟨q * ((⟨u, hu⟩ : localGroup D z) * q *
    (⟨u, hu⟩ : localGroup D z)⁻¹)⁻¹,
    (CFSG.pCore 2 (localGroup D z)).mul_mem hq
      ((CFSG.pCore 2 (localGroup D z)).inv_mem hconj), ?_⟩
  show (q : G) * (u * (q : G) * u⁻¹)⁻¹ = a * u⁻¹
  rw [h]

omit [Finite G] in
theorem exists_twoSubgroup_thirdKind (hS : Setup G D)
    {u c a t : G} {m : ℕ} (htri : IsTriangle D u c a) (hm : Odd m)
    (hord : orderOf (u * a * c) = 2 * m) (htdef : (u * a * c) ^ m = t) :
    ∃ P : Subgroup G, IsPGroup 2 P ∧ (∀ p ∈ P, Commute p u ∧ Commute p a) ∧
      u * a * t ∈ P := by
  obtain ⟨htt, -, htu, hta, -, huatD⟩ := htri.third_kind hS.oddT hS.normal hm hord
  rw [htdef] at htt htu hta huatD
  have hua : Commute u a := htri.2.2.2.2.1; have huD : u ∈ D := htri.1
  have haD : a ∈ D := htri.2.1
  have hu2 : u * u = 1 := hS.oddT.mul_self_eq_one huD
  have ha2 : a * a = 1 := hS.oddT.mul_self_eq_one haD
  have huaut : Commute u (u * a * t) :=
    ((Commute.refl u).mul_right hua).mul_right htu.symm
  have haut : Commute a (u * a * t) :=
    (hua.symm.mul_right (Commute.refl a)).mul_right hta.symm
  have huat_comm : Commute (u * a) t := Commute.mul_left htu.symm hta.symm
  have hua2 : (u * a) * (u * a) = 1 := by
    calc (u * a) * (u * a) = u * (a * u) * a := by group
      _ = u * (u * a) * a := by rw [hua.eq]
      _ = (u * u) * (a * a) := by group
      _ = 1 := by rw [hu2, ha2, one_mul]
  have huat2 : (u * a * t) * (u * a * t) = 1 := by
    calc (u * a * t) * (u * a * t) = (u * a) * (t * (u * a)) * t := by group
      _ = (u * a) * ((u * a) * t) * t := by rw [← huat_comm.eq]
      _ = ((u * a) * (u * a)) * (t * t) := by group
      _ = 1 := by rw [hua2, htt, one_mul]
  have hpair : ({u, a, u * a * t} : Set G).Pairwise Commute := by
    have h1 := hua; have h2 := huaut; have h3 := haut
    intro s hs r hr _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs hr
    rcases hs with rfl | rfl | rfl <;> rcases hr with rfl | rfl | rfl <;>
      first | exact Commute.refl _ | assumption | exact h1.symm | exact h2.symm | exact h3.symm
  have hP : IsPGroup 2 (Subgroup.closure ({u, a, u * a * t} : Set G)) := by
    refine isPGroup_closure_of_pairwise hpair ?_
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact hu2
    · exact ha2
    · exact huat2
  have hgen : ∀ r ∈ ({u, a, u * a * t} : Set G), Commute r u ∧ Commute r a := by
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with hr | hr | hr <;> rw [hr]
    · exact ⟨Commute.refl u, hua⟩
    · exact ⟨hua.symm, Commute.refl a⟩
    · exact ⟨huaut.symm, haut.symm⟩
  have hPC : ∀ p ∈ Subgroup.closure ({u, a, u * a * t} : Set G),
      Commute p u ∧ Commute p a := by
    intro p hp
    constructor
    · exact commute_of_mem_closure (S := {u, a, u * a * t}) (T := {u})
        (fun r hr k hk => by
          rw [Set.mem_singleton_iff] at hk
          rw [hk]
          exact (hgen r hr).1) hp (Subgroup.subset_closure rfl)
    · exact commute_of_mem_closure (S := {u, a, u * a * t}) (T := {a})
        (fun r hr k hk => by
          rw [Set.mem_singleton_iff] at hk
          rw [hk]
          exact (hgen r hr).2) hp (Subgroup.subset_closure rfl)
  exact ⟨Subgroup.closure ({u, a, u * a * t} : Set G), hP, hPC,
    Subgroup.subset_closure (by simp)⟩

theorem exists_conj_mem_sylow_thirdKind (hS : Setup G D)
    {u c a t : G} {m : ℕ} (htri : IsTriangle D u c a) (hm : Odd m)
    (hord : orderOf (u * a * c) = 2 * m) (htdef : (u * a * c) ^ m = t)
    {S₀ : Sylow 2 G} (huS : u ∈ S₀) (haS : a ∈ S₀) :
    ∃ g : G, g * u * g⁻¹ = u ∧ g * a * g⁻¹ = a ∧
      g * (u * a * t) * g⁻¹ ∈ D ∩ (S₀ : Set G) := by
  obtain ⟨P, hP, hPC, huatP⟩ := exists_twoSubgroup_thirdKind hS htri hm hord htdef
  have huD : u ∈ D := htri.1
  have haD : a ∈ D := htri.2.1
  obtain ⟨-, -, -, -, -, huatD⟩ := htri.third_kind hS.oddT hS.normal hm hord
  rw [htdef] at huatD
  have hL : ∀ s ∈ D ∩ (S₀ : Set G), Commute s u ∧ Commute s a := fun s hs =>
    ⟨hS.oddT.commute_of_isPGroup S₀.isPGroup' hs.1 huD hs.2 huS,
      hS.oddT.commute_of_isPGroup S₀.isPGroup' hs.1 haD hs.2 haS⟩
  obtain ⟨g, hgu, hga, hgP⟩ := exists_conj_mem_of_isPGroup hS.normal S₀ hL hP hPC
  refine ⟨g, by rw [hgu.eq, mul_inv_cancel_right], by rw [hga.eq, mul_inv_cancel_right], ?_⟩
  exact hgP (u * a * t) huatP huatD

theorem exists_conj_involution_thirdKind (hS : Setup G D)
    {u c a t : G} {m : ℕ} (htri : IsTriangle D u c a) (hm : Odd m)
    (hord : orderOf (u * a * c) = 2 * m) (htdef : (u * a * c) ^ m = t)
    {S₀ : Sylow 2 G} (huS : u ∈ S₀) (haS : a ∈ S₀) :
    ∃ (g t' c' : G), g * u * g⁻¹ = u ∧ g * a * g⁻¹ = a ∧
      g * t * g⁻¹ = t' ∧ g * c * g⁻¹ = c' ∧
      IsTriangle D u c' a ∧ orderOf (u * a * c') = 2 * m ∧ (u * a * c') ^ m = t' ∧
      u * a * t' ∈ D ∩ (S₀ : Set G) := by
  obtain ⟨g, hgu', hga', huatS⟩ :=
    exists_conj_mem_sylow_thirdKind hS htri hm hord htdef huS haS
  have huatg : g * (u * a * t) * g⁻¹ = u * a * (g * t * g⁻¹) := by
    calc g * (u * a * t) * g⁻¹ = (g * u * g⁻¹) * (g * a * g⁻¹) * (g * t * g⁻¹) := by group
      _ = u * a * (g * t * g⁻¹) := by rw [hgu', hga']
  have huatS' : u * a * (g * t * g⁻¹) ∈ D ∩ (S₀ : Set G) := by
    rw [← huatg]
    exact huatS
  have htri' : IsTriangle D u (g * c * g⁻¹) a := by
    have h := isTriangle_conj (g := g) hS.normal htri
    rwa [hgu', hga'] at h
  have hconjc : g * (u * a * c) * g⁻¹ = u * a * (g * c * g⁻¹) := by
    calc g * (u * a * c) * g⁻¹ = (g * u * g⁻¹) * (g * a * g⁻¹) * (g * c * g⁻¹) := by group
      _ = u * a * (g * c * g⁻¹) := by rw [hgu', hga']
  have hord' : orderOf (u * a * (g * c * g⁻¹)) = 2 * m := by
    rw [← hconjc, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hord]
  have ht'def : (u * a * (g * c * g⁻¹)) ^ m = g * t * g⁻¹ := by
    rw [← hconjc, ← MulAut.conj_apply, ← map_pow, htdef, MulAut.conj_apply]
  exact ⟨g, g * t * g⁻¹, g * c * g⁻¹, hgu', hga', rfl, rfl, htri', hord', ht'def, huatS'⟩

omit [Finite G] in
theorem transitive_conj_of_conj_eq (hS : Setup G D) {u t g : G}
    (hgu : g * u * g⁻¹ = u)
    (htrans : ∀ x ∈ centSet D t, ∃ k ∈ localGroup D t, k * u * k⁻¹ = x) :
    ∀ x ∈ centSet D (g * t * g⁻¹),
      ∃ k ∈ localGroup D (g * t * g⁻¹), k * u * k⁻¹ = x := by
  have hcomm : Commute g u := by
    rw [commute_iff_eq]
    calc g * u = g * u * g⁻¹ * g := by group
      _ = u * g := by rw [hgu]
  have hgu_back : g⁻¹ * u * g = u := by
    calc g⁻¹ * u * g = g⁻¹ * (u * g) := by group
      _ = g⁻¹ * (g * u) := by rw [← hcomm.eq]
      _ = u := by group
  intro x hx
  have hxback : g⁻¹ * x * g ∈ centSet D t := by
    refine ⟨by simpa using hS.normal g⁻¹ x hx.1, ?_⟩
    have h := (Commute.conj_iff g⁻¹).mpr hx.2
    simpa [mul_assoc] using h
  obtain ⟨k, hk, hku⟩ := htrans _ hxback
  refine ⟨g * k * g⁻¹, ?_, ?_⟩
  · have hkz : k ∈ localGroup D (g⁻¹ * (g * t * g⁻¹) * (g⁻¹)⁻¹) := by
      have hgt : g⁻¹ * (g * t * g⁻¹) * (g⁻¹)⁻¹ = t := by group
      rwa [hgt]
    have h' := conj_mem_localGroup_of_mem hS.normal (z := g * t * g⁻¹) (k := g⁻¹)
      (x := k) hkz
    simpa using h'
  · calc (g * k * g⁻¹) * u * (g * k * g⁻¹)⁻¹ =
        g * (k * (g⁻¹ * u * g) * k⁻¹) * g⁻¹ := by group
      _ = g * (k * u * k⁻¹) * g⁻¹ := by rw [hgu_back]
      _ = g * (g⁻¹ * x * g) * g⁻¹ := by rw [hku]
      _ = x := by group

omit [Finite G] in
theorem exists_two_mem_D_mul_of_vertex (hS : Setup G D)
    {u c a t x : G} (htri : IsTriangle D u c a) {m : ℕ} (hm : Odd m)
    (hord : orderOf (u * a * c) = 2 * m) (htdef : (u * a * c) ^ m = t)
    (hx : x = u ∨ x = a ∨ x = u * a * t) :
    ∃ p ∈ D, ∃ q ∈ D, p ≠ q ∧ Commute p q ∧ x * t = p * q := by
  obtain ⟨htt, -, htu, hta, htc, huatD⟩ := htri.third_kind hS.oddT hS.normal hm hord
  rw [htdef] at htt htu hta htc huatD
  have hua : Commute u a := htri.2.2.2.2.1
  have huD : u ∈ D := htri.1
  have haD : a ∈ D := htri.2.1
  have hu2 : u * u = 1 := hS.oddT.mul_self_eq_one huD
  have ha2 : a * a = 1 := hS.oddT.mul_self_eq_one haD
  have huaut : Commute u (u * a * t) :=
    ((Commute.refl u).mul_right hua).mul_right htu.symm
  have haut : Commute a (u * a * t) :=
    (hua.symm.mul_right (Commute.refl a)).mul_right hta.symm
  have hu_t : u * t = a * (u * a * t) := by
    calc u * t = u * (a * a) * t := by rw [ha2, mul_one]
      _ = u * a * (a * t) := by group
      _ = a * u * (a * t) := by rw [hua.eq]
      _ = a * (u * a * t) := by group
  have ha_t : a * t = u * (u * a * t) := by
    calc a * t = (u * u) * a * t := by rw [hu2, one_mul]
      _ = u * (u * a * t) := by group
  have huat_t : (u * a * t) * t = u * a := by
    calc (u * a * t) * t = u * a * (t * t) := by group
      _ = u * a := by rw [htt, mul_one]
  have hne_u : u ≠ u * a * t := by
    intro h
    have h1 : a * t = 1 := by
      apply mul_left_cancel (a := u)
      calc u * (a * t) = u * a * t := by group
        _ = u := h.symm
        _ = u * 1 := (mul_one u).symm
    have ht_a : t = a := by
      calc t = a * (a * t) := by rw [← mul_assoc, ha2, one_mul]
        _ = a * 1 := by rw [h1]
        _ = a := mul_one _
    exact htri.2.2.2.2.2.2 (ht_a ▸ htc)
  have hne_a : a ≠ u * a * t := by
    intro h
    have h1 : a * t = u * a := by
      calc a * t = (u * a * t) * t := by rw [← h]
        _ = u * a * (t * t) := by group
        _ = u * a := by rw [htt, mul_one]
    have ht_u : t = u := by
      calc t = a * (a * t) := by rw [← mul_assoc, ha2, one_mul]
        _ = a * (u * a) := by rw [h1]
        _ = a * (a * u) := by rw [← hua.eq]
        _ = (a * a) * u := by group
        _ = u := by rw [ha2, one_mul]
    exact htri.2.2.2.2.2.1 (ht_u ▸ htc)
  rcases hx with hx | hx | hx <;> rw [hx]
  · exact ⟨a, haD, u * a * t, huatD, hne_a, haut, hu_t⟩
  · exact ⟨u, huD, u * a * t, huatD, hne_u, huaut, ha_t⟩
  · exact ⟨u, huD, a, haD, htri.2.2.2.1, hua, huat_t⟩

omit [Finite G] in
theorem exists_two_mem_D_mul_of_conj (hS : Setup G D)
    {u c a t d e : G} (htri : IsTriangle D u c a) {m : ℕ} (hm : Odd m)
    (hord : orderOf (u * a * c) = 2 * m) (htdef : (u * a * c) ^ m = t)
    {x y : G} (hx : x = u ∨ x = a ∨ x = u * a * t) (hyt : Commute y t)
    (hyx : y * x * y⁻¹ = d) (heq : t = d * e) :
    ∃ r ∈ D, ∃ s ∈ D, r ≠ s ∧ Commute r s ∧ e = r * s := by
  obtain ⟨p, hpD, q, hqD, hpq, hpqc, hxq⟩ :=
    exists_two_mem_D_mul_of_vertex hS htri hm hord htdef hx
  have huatD : u * a * t ∈ D := by
    have h := (htri.third_kind hS.oddT hS.normal hm hord).2.2.2.2.2
    rwa [htdef] at h
  have hxD : x ∈ D := by
    rcases hx with hx | hx | hx <;> rw [hx]
    · exact htri.1
    · exact htri.2.1
    · exact huatD
  have hdD : d ∈ D := by rw [← hyx]; exact hS.normal y x hxD
  have hdd : d * d = 1 := hS.oddT.mul_self_eq_one hdD
  have het : e = d * t := by
    rw [heq]
    calc e = (d * d) * e := by rw [hdd, one_mul]
      _ = d * (d * e) := by group
  have heyr : e = y * (x * t) * y⁻¹ := by
    rw [het]
    calc d * t = (y * x * y⁻¹) * t := by rw [← hyx]
      _ = y * x * (y⁻¹ * t) := by group
      _ = y * x * (t * y⁻¹) := by rw [hyt.inv_left.eq]
      _ = y * (x * t) * y⁻¹ := by group
  set r : G := y * p * y⁻¹ with hrdef
  set s : G := y * q * y⁻¹ with hsdef
  have hrD : r ∈ D := by rw [hrdef]; exact hS.normal y p hpD
  have hsD : s ∈ D := by rw [hsdef]; exact hS.normal y q hqD
  have hrs : Commute r s := by
    rw [hrdef, hsdef]
    exact (Commute.conj_iff y).mpr hpqc
  have hne : r ≠ s := by
    intro h
    apply hpq
    have h' := congrArg (fun z => y⁻¹ * z * y) h
    simpa [hrdef, hsdef, mul_assoc] using h'
  refine ⟨r, hrD, s, hsD, hne, hrs, ?_⟩
  rw [heyr, hxq, hrdef, hsdef]
  group

omit [Finite G] in
theorem classIn_le_localGroup {z w : G} {S₀ : Sylow 2 G}
    (hwC : w ∈ centSet D z) (hLz : ∀ s ∈ D ∩ (S₀ : Set G), Commute s z) :
    Subgroup.closure (insert w (D ∩ (S₀ : Set G))) ≤ localGroup D z := by
  rw [Subgroup.closure_le]
  rintro y (rfl | hy)
  · exact mem_localGroup_of_mem hwC
  · exact mem_localGroup_of_mem ⟨hy.1, hLz y hy⟩

omit [Finite G] in
theorem thirdKind_z_not_mem_D (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n)
    (hord : orderOf (u * v * w) = 2 * n) {z : G} (hzdef : (u * v * w) ^ n = z)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x) :
    z ∉ D := by
  intro hzD'
  obtain ⟨-, -, hzu, -, hzw, -⟩ := htri.third_kind hS.oddT hS.normal hn hord
  rw [hzdef] at hzu hzw
  have hzC : z ∈ centSet D z := ⟨hzD', Commute.refl z⟩
  obtain ⟨k, hkK, hkz⟩ := htrans z hzC
  have hkcomm : Commute k z := commute_of_mem_localGroup hkK
  have huz : u = z := by
    calc u = k⁻¹ * (k * u * k⁻¹) * k := by group
      _ = k⁻¹ * z * k := by rw [hkz]
      _ = z := by
        calc k⁻¹ * z * k = k⁻¹ * (z * k) := by group
          _ = k⁻¹ * (k * z) := by rw [hkcomm.eq]
          _ = z := by group
  exact htri.2.2.2.2.2.1 (huz.symm ▸ hzw)

omit [Finite G] in
theorem commute_of_mem_inter_sylow_of_thirdKind (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n)
    (hord : orderOf (u * v * w) = 2 * n) {z : G} (hzdef : (u * v * w) ^ n = z)
    {S₀ : Sylow 2 G} (huS : u ∈ S₀) (hvS : v ∈ S₀) (hbS : u * v * z ∈ S₀) :
    ∀ s ∈ D ∩ (S₀ : Set G), Commute s z := by
  obtain ⟨-, -, -, -, -, hbD⟩ := htri.third_kind hS.oddT hS.normal hn hord
  rw [hzdef] at hbD
  have hzabd : z = u * v * (u * v * z) := by
    calc z = (u * v) * (u * v) * z := by
          rw [IsTriangle.uv_mul_self hS.oddT htri, one_mul]
      _ = u * v * (u * v * z) := by group
  intro s hs
  rw [hzabd]
  exact ((hS.oddT.commute_of_isPGroup S₀.isPGroup' hs.1 htri.1 hs.2 huS).mul_right
    (hS.oddT.commute_of_isPGroup S₀.isPGroup' hs.1 htri.2.1 hs.2 hvS)).mul_right
    (hS.oddT.commute_of_isPGroup S₀.isPGroup' hs.1 hbD hs.2 hbS)

structure ClassInCore (D : Set G) (u w v z : G) (S₀ : Sylow 2 G) where
  X : Subgroup G
  hX : X = Subgroup.closure (insert w (D ∩ (S₀ : Set G)))
  EX : Set X
  uX : X
  huX : (uX : G) = u
  vX : X
  hvX : (vX : G) = v
  wX : X
  hwX : (wX : G) = w
  hLX : ∀ s ∈ D ∩ (S₀ : Set G), s ∈ X
  hmemX : ∀ s (hs : s ∈ D ∩ (S₀ : Set G)), (⟨s, hLX s hs⟩ : X) ∈ EX
  hwE : wX ∈ EX
  hEXD : ∀ k ∈ EX, (k : G) ∈ D
  hSX : Setup X EX
  hdiscX : Disconnected EX
  hXK : X ≤ localGroup D z
  hzD : z ∉ D
  hLz : ∀ s ∈ D ∩ (S₀ : Set G), Commute s z
  hzabd : z = u * v * (u * v * z)
  hgenX : Subgroup.closure (insert wX {x : X | ∃ s : G,
    ∃ hs : s ∈ D ∩ (S₀ : Set G), x = ⟨s, hLX s hs⟩}) = ⊤

structure ClassInBase (D : Set G) (u w v z : G) (S₀ : Sylow 2 G) where
  core : ClassInCore D u w v z S₀
  hnpc : NoPerfectCentralExt core.X (CFSG.pCore 2 core.X)
  hzX : z ∈ core.X

structure ClassInSetup (D : Set G) (u w v z : G) (n : ℕ) (S₀ : Sylow 2 G) where
  base : ClassInBase D u w v z S₀
  T : Sylow 2 base.core.X
  hLT : ∀ s (hs : s ∈ D ∩ (S₀ : Set G)), (⟨s, base.core.hLX s hs⟩ : base.core.X) ∈ T
  hKH : ThirdKindHyp base.core.X base.core.EX T base.core.uX base.core.wX base.core.vX n

noncomputable def ClassInCore.ofBender (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n) {z : G} (hzdef : (u * v * w) ^ n = z)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x)
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z)))
    {S₀ : Sylow 2 G} (huS : u ∈ S₀) (hvS : v ∈ S₀) (hbS : u * v * z ∈ S₀) :
    ClassInCore D u w v z S₀ := by
  classical
  obtain ⟨hzz, -, hzu, hzv, hzw, hbD⟩ := htri.third_kind hS.oddT hS.normal hn hord
  obtain ⟨huC, hvC, hwC, hdC⟩ := thirdKind_mem_centSet hS htri hn hord
  rw [hzdef] at hzz hzu hzv hzw hbD huC hvC hwC hdC
  have hzD : z ∉ D := thirdKind_z_not_mem_D hS htri hn hord hzdef htrans
  have hzabd : z = u * v * (u * v * z) := by
    calc z = (u * v) * (u * v) * z := by
          rw [IsTriangle.uv_mul_self hS.oddT htri, one_mul]
      _ = u * v * (u * v * z) := by group
  have hLz : ∀ s ∈ D ∩ (S₀ : Set G), Commute s z :=
    commute_of_mem_inter_sylow_of_thirdKind hS htri hn hord hzdef huS hvS hbS
  have hLx : ∀ s ∈ D ∩ (S₀ : Set G), ¬ Commute s w := fun s hs =>
    not_commute_of_mem_sylow_of_bender hS htri hn hn1 hord hzdef htrans hB
      huS hvS hbS hzabd hbD hs.1 hs.2
  set X : Subgroup G := Subgroup.closure (insert w (D ∩ (S₀ : Set G))) with hXdef
  let wX : X := ⟨w, Subgroup.subset_closure (Set.mem_insert w (D ∩ (S₀ : Set G)))⟩
  let EX : Set X := classIn X wX
  obtain ⟨hSX, hmemX⟩ := setup_classIn hS htri.2.2.1 Set.inter_subset_left hLx
  have hLX : ∀ s ∈ D ∩ (S₀ : Set G), s ∈ X := fun s hs =>
    Subgroup.subset_closure (Set.mem_insert_of_mem w hs)
  have hdiscX : Disconnected EX := by
    simpa only [X, EX, wX] using disconnected_classIn_of_bender hS htri hn hn1 hord
      hzdef htrans hB huS hvS hbS hzabd hbD hLx
  have hXK : X ≤ localGroup D z := classIn_le_localGroup hwC hLz
  have hEXD : ∀ k ∈ EX, (k : G) ∈ D := fun k hk => by
    obtain ⟨c, rfl⟩ := isConj_iff.mp hk
    exact hS.conj_mem (c : G) htri.2.2.1
  have hgenX : Subgroup.closure (insert wX {x : X | ∃ s : G,
      ∃ hs : s ∈ D ∩ (S₀ : Set G), x = ⟨s, hLX s hs⟩}) = ⊤ := by
    rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage
      (k := insert w (D ∩ (S₀ : Set G)))]
    refine Subgroup.closure_mono ?_; rintro ⟨r, hr⟩ (hr' | hr')
    · exact Or.inl (Subtype.ext hr')
    · exact Or.inr ⟨r, hr', rfl⟩
  exact
    { X := X
      hX := hXdef
      EX := EX
      uX := ⟨u, hLX u ⟨htri.1, huS⟩⟩
      huX := rfl
      vX := ⟨v, hLX v ⟨htri.2.1, hvS⟩⟩
      hvX := rfl
      wX := wX
      hwX := rfl
      hLX := hLX
      hmemX := hmemX
      hwE := IsConj.refl wX
      hEXD := hEXD
      hSX := hSX
      hdiscX := hdiscX
      hXK := hXK
      hzD := hzD
      hLz := hLz
      hzabd := hzabd
      hgenX := hgenX }

omit [Finite G] in
theorem classIn_closure_eq_top {u w v z : G} {S₀ : Sylow 2 G}
    (base : ClassInBase D u w v z S₀)
    {T : Sylow 2 base.core.X}
    (hLT : ∀ s (hs : s ∈ D ∩ (S₀ : Set G)),
      (⟨s, base.core.hLX s hs⟩ : base.core.X) ∈ T) :
    Subgroup.closure (insert base.core.wX (base.core.EX ∩ (T : Set base.core.X))) = ⊤ := by
  have hsubset : insert base.core.wX {x : base.core.X | ∃ s : G,
      ∃ hs : s ∈ D ∩ (S₀ : Set G), x = ⟨s, base.core.hLX s hs⟩} ⊆
      insert base.core.wX (base.core.EX ∩ (T : Set base.core.X)) := by
    intro x hx
    by_cases hxw : x = base.core.wX
    · rw [hxw]
      exact Set.mem_insert _ _
    · apply Set.mem_insert_of_mem
      have hxS : x ∈ {x : base.core.X | ∃ s : G,
          ∃ hs : s ∈ D ∩ (S₀ : Set G), x = ⟨s, base.core.hLX s hs⟩} := by
        simpa [Set.mem_insert_iff, hxw] using hx
      obtain ⟨s, hs, hxs⟩ := hxS
      rw [hxs]
      exact ⟨base.core.hmemX s hs, hLT s hs⟩
  exact top_unique (by
    rw [← base.core.hgenX]
    exact Subgroup.closure_mono hsubset)


omit [Finite G] in
theorem classIn_thirdKindHyp {u w v z : G} {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    {S₀ : Sylow 2 G} (base : ClassInBase D u w v z S₀) (T : Sylow 2 base.core.X)
    (hLT : ∀ s (hs : s ∈ D ∩ (S₀ : Set G)),
      (⟨s, base.core.hLX s hs⟩ : base.core.X) ∈ T)
    (huE : base.core.uX ∈ base.core.EX) (hvE : base.core.vX ∈ base.core.EX)
    (hne : base.core.uX ≠ base.core.vX) (huv : Commute base.core.uX base.core.vX)
    (huw : ¬ Commute base.core.uX base.core.wX)
    (hvw : ¬ Commute base.core.vX base.core.wX)
    (hordX : orderOf (base.core.uX * base.core.vX * base.core.wX) = 2 * n)
    (huT : base.core.uX ∈ T) (hvT : base.core.vX ∈ T)
    (hzT : (base.core.uX * base.core.vX * base.core.wX) ^ n ∈ T) :
    ThirdKindHyp base.core.X base.core.EX T base.core.uX base.core.wX base.core.vX n :=
  { setup := base.core.hSX
    tri := ⟨huE, hvE, base.core.hwE, hne, huv, huw, hvw⟩
    odd := hn
    one_lt := hn1
    order := hordX
    a_mem := huT
    c_mem := hvT
    z_mem := hzT
    gen := classIn_closure_eq_top base hLT
    npc := base.hnpc }

noncomputable def ClassInSetup.ofBase
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n) {z : G} (hzdef : (u * v * w) ^ n = z)
    {S₀ : Sylow 2 G} (huS : u ∈ S₀) (hvS : v ∈ S₀) (hbS : u * v * z ∈ S₀)
    (base : ClassInBase D u w v z S₀) : ClassInSetup D u w v z n S₀ := by
  classical
  have hP' : IsPGroup 2 ((S₀ : Subgroup G).subgroupOf base.core.X) :=
    S₀.isPGroup'.comap_subtype
  choose T hT using hP'.exists_le_sylow
  have hLT : ∀ s (hs : s ∈ D ∩ (S₀ : Set G)),
      (⟨s, base.core.hLX s hs⟩ : base.core.X) ∈ T := fun s hs =>
    hT (Subgroup.mem_subgroupOf.mpr hs.2)
  have huXE : base.core.uX = (⟨u, base.core.hLX u ⟨htri.1, huS⟩⟩ : base.core.X) :=
    Subtype.ext base.core.huX
  have hvXE : base.core.vX = (⟨v, base.core.hLX v ⟨htri.2.1, hvS⟩⟩ : base.core.X) :=
    Subtype.ext base.core.hvX
  have huE : base.core.uX ∈ base.core.EX := by
    rw [huXE]; exact base.core.hmemX u ⟨htri.1, huS⟩
  have hvE : base.core.vX ∈ base.core.EX := by
    rw [hvXE]; exact base.core.hmemX v ⟨htri.2.1, hvS⟩
  have hne : base.core.uX ≠ base.core.vX := by
    intro h
    exact htri.2.2.2.1 (by simpa [base.core.huX, base.core.hvX] using congrArg Subtype.val h)
  have huv : Commute base.core.uX base.core.vX :=
    (commute_iff_eq _ _).mpr (Subtype.ext (by
      simpa [base.core.huX, base.core.hvX] using htri.2.2.2.2.1.eq))
  have huw : ¬ Commute base.core.uX base.core.wX := fun h =>
    htri.2.2.2.2.2.1 (by simpa [base.core.huX, base.core.hwX] using commute_coe_iff.mpr h)
  have hvw : ¬ Commute base.core.vX base.core.wX := fun h =>
    htri.2.2.2.2.2.2 (by simpa [base.core.hvX, base.core.hwX] using commute_coe_iff.mpr h)
  have hordX : orderOf (base.core.uX * base.core.vX * base.core.wX) = 2 * n := by
    rw [← Subgroup.orderOf_coe]
    simpa [base.core.huX, base.core.hvX, base.core.hwX] using hord
  have hzS : z ∈ S₀ := by
    rw [base.core.hzabd]
    exact S₀.mul_mem (S₀.mul_mem huS hvS) hbS
  have hzT : (base.core.uX * base.core.vX * base.core.wX) ^ n ∈ T := by
    have h1 : (base.core.uX * base.core.vX * base.core.wX) ^ n =
        (⟨z, base.hzX⟩ : base.core.X) := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow]
      simpa [base.core.huX, base.core.hvX, base.core.hwX] using hzdef
    rw [h1]
    exact hT (Subgroup.mem_subgroupOf.mpr hzS)
  have hgen : Subgroup.closure (insert base.core.wX
      (base.core.EX ∩ (T : Set base.core.X))) = ⊤ :=
    classIn_closure_eq_top base hLT
  have huT : base.core.uX ∈ T := by
    rw [huXE]
    exact hLT u ⟨htri.1, huS⟩
  have hvT : base.core.vX ∈ T := by
    rw [hvXE]
    exact hLT v ⟨htri.2.1, hvS⟩
  have hKH := classIn_thirdKindHyp hn hn1 base T hLT huE hvE hne huv huw hvw hordX huT hvT hzT
  exact
    { base := base
      T := T
      hLT := hLT
      hKH := hKH }

omit [Finite G] in
theorem ClassInSetup.exists_mul_eq_of_eq_mul {u w v z : G} {n : ℕ} {S₀ : Sylow 2 G}
    (setup : ClassInSetup D u w v z n S₀) {a f : G}
    (huD : u ∈ D) (huS : u ∈ S₀) (haD : a ∈ D) (haS : a ∈ S₀) (hfD : f ∈ D) (hfS : f ∈ S₀)
    {p1 p2 : setup.base.core.X}
    (hp1E : p1 ∈ setup.base.core.EX)
    (hp2 : p2 ∈ CFSG.pCore 2 setup.base.core.X ⊓ Subgroup.center setup.base.core.X)
    (heq' : setup.base.core.uX *
        (⟨f, setup.base.core.hLX f ⟨hfD, hfS⟩⟩ : setup.base.core.X) *
        (⟨a, setup.base.core.hLX a ⟨haD, haS⟩⟩ : setup.base.core.X) = p1 * p2) :
    ∃ d e : G, u * f * a = d * e ∧ Commute d e ∧ d ∈ centSet D z ∧ ¬ Commute d w ∧
      e ∈ localGroup D z ∧ Commute e w ∧ ∀ s ∈ D ∩ (S₀ : Set G), Commute e s := by
  set fX : setup.base.core.X := ⟨f, setup.base.core.hLX f ⟨hfD, hfS⟩⟩ with hfXdef
  set aX : setup.base.core.X := ⟨a, setup.base.core.hLX a ⟨haD, haS⟩⟩ with haXdef
  set d : G := (p1 : G) with hddef
  set e : G := (p2 : G) with hedef
  have hprod : u * f * a = d * e := by
    have h := congrArg (fun z : setup.base.core.X => (z : G)) heq'
    simpa [fX, aX, d, e, setup.base.core.huX, setup.base.core.hvX,
      setup.base.core.hwX] using h
  have hcomm : Commute d e := by
    have h : Commute p1 p2 := Subgroup.mem_center_iff.mp hp2.2 p1
    have h' := commute_coe_iff.mpr h
    simpa [d, e] using h'
  have hdD : d ∈ D := setup.base.core.hEXD p1 hp1E
  have hdK : d ∈ localGroup D z := setup.base.core.hXK p1.2
  have hdc : d ∈ centSet D z := ⟨hdD, commute_of_mem_localGroup hdK⟩
  have hp2T : p2 ∈ setup.T := ThirdKindHyp.pCore_le hp2.1
  have huXE : setup.base.core.uX =
      (⟨u, setup.base.core.hLX u ⟨huD, huS⟩⟩ : setup.base.core.X) :=
    Subtype.ext setup.base.core.huX
  have huT : setup.base.core.uX ∈ setup.T := by
    rw [huXE]
    exact setup.hLT u ⟨huD, huS⟩
  have hp1T : p1 ∈ setup.T := by
    have hprodT : setup.base.core.uX * fX * aX ∈ setup.T :=
      setup.T.mul_mem (setup.T.mul_mem huT (setup.hLT f ⟨hfD, hfS⟩))
        (setup.hLT a ⟨haD, haS⟩)
    have hp1eq : p1 = setup.base.core.uX * fX * aX * p2⁻¹ := by
      calc p1 = p1 * p2 * p2⁻¹ := by group
        _ = setup.base.core.uX * fX * aX * p2⁻¹ := by rw [← heq']
    rw [hp1eq]
    exact setup.T.mul_mem hprodT (setup.T.inv_mem hp2T)
  have hnc : ¬ Commute p1 setup.base.core.wX := setup.hKH.not_commute_b ⟨hp1E, hp1T⟩
  have hdnc : ¬ Commute d w := by
    intro h
    have h' : Commute (p1 : G) (setup.base.core.wX : G) := by
      simpa [d, setup.base.core.hwX] using h
    exact hnc (commute_coe_iff.mp h')
  have heK : e ∈ localGroup D z := setup.base.core.hXK p2.2
  have hew : Commute e w := by
    have h := commute_coe_iff.mpr
      (Subgroup.mem_center_iff.mp hp2.2 setup.base.core.wX)
    simpa [e, setup.base.core.hwX] using h.symm
  have hes : ∀ s ∈ D ∩ (S₀ : Set G), Commute e s := by
    intro s hs
    have hsX : s ∈ setup.base.core.X := setup.base.core.hLX s hs
    have h := commute_coe_iff.mpr
      (Subgroup.mem_center_iff.mp hp2.2 ⟨s, hsX⟩)
    simpa [e] using h.symm
  exact ⟨d, e, hprod, hcomm, hdc, hdnc, heK, hew, hes⟩

section Certificates


noncomputable def ClassInBase.ofCore (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n)
    (hord : orderOf (u * v * w) = 2 * n) {z : G} (hzdef : (u * v * w) ^ n = z)
    {S₀ : Sylow 2 G} (huS : u ∈ S₀) (hvS : v ∈ S₀) (hbS : u * v * z ∈ S₀)
    (core : ClassInCore D u w v z S₀) : ClassInBase D u w v z S₀ := by
  classical
  have hD := hS.oddT
  obtain ⟨hzz, -, -, -, hzw, hbD⟩ := htri.third_kind hD hS.normal hn hord
  rw [hzdef] at hzz hzw hbD
  have hzX : z ∈ core.X := by
    have h : u * v * (u * v * z) ∈ core.X :=
      core.X.mul_mem (core.X.mul_mem (core.hLX u ⟨htri.1, huS⟩)
        (core.hLX v ⟨htri.2.1, hvS⟩)) (core.hLX (u * v * z) ⟨hbD, hbS⟩)
    rwa [← core.hzabd] at h
  have hzcomm : ∀ g ∈ core.X, Commute g z := by
    intro g hg
    have hle : core.X ≤ Subgroup.centralizer {z} := by
      rw [core.hX, Subgroup.closure_le]
      rintro y (rfl | hy)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hzw.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (core.hLz y hy).eq
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  set z' : core.X := ⟨z, hzX⟩ with hz'def
  have hz'c : z' ∈ Subgroup.center core.X := Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (hzcomm g g.2).eq
  have hz'z' : z' * z' = 1 := Subtype.ext hzz
  have hz'E : z' ∉ core.EX := fun h => core.hzD (core.hEXD z' h)
  have hzp : (Subgroup.zpowers z').Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz'c)
  set u' : core.X := core.uX with hu'def
  set v' : core.X := core.vX with hv'def
  have huX_eq : u' = (⟨u, core.hLX u ⟨htri.1, huS⟩⟩ : core.X) := by
    apply Subtype.ext
    exact core.huX
  have hvX_eq : v' = (⟨v, core.hLX v ⟨htri.2.1, hvS⟩⟩ : core.X) := by
    apply Subtype.ext
    exact core.hvX
  have hu'E : u' ∈ core.EX := by
    rw [huX_eq]
    exact core.hmemX u ⟨htri.1, huS⟩
  have hv'E : v' ∈ core.EX := by
    rw [hvX_eq]
    exact core.hmemX v ⟨htri.2.1, hvS⟩
  have huvz : u' * v' * z' ∈ core.EX := by
    convert core.hmemX (u * v * z) ⟨hbD, hbS⟩ using 2
    simp [u', v', z', core.huX, core.hvX]
  have hnpc : NoPerfectCentralExt core.X (CFSG.pCore 2 core.X) :=
    CentralQuot.noPerfectCentralExt hz'c hz'z' core.hSX hz'E core.hdiscX hu'E hv'E
      (fun h => htri.2.2.2.1 (by
        simpa [u', v', core.huX, core.hvX] using congrArg Subtype.val h))
      (by
        have h := htri.2.2.2.2.1
        exact commute_coe_iff.mp (by simpa [u', v', core.huX, core.hvX] using h))
      huvz
  exact { core := core, hnpc := hnpc, hzX := hzX }


theorem exists_mul_eq_of_mem_sylow_of_bender (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n) {z : G} (hzdef : (u * v * w) ^ n = z)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x)
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z)))
    {S₀ : Sylow 2 G} (huS : u ∈ S₀) (hvS : v ∈ S₀) (hbS : u * v * z ∈ S₀)
    {a f : G} (haD : a ∈ D) (haS : a ∈ S₀)
    (hau : a * u⁻¹ ∈ (CFSG.pCore 2 (localGroup D z)).map (localGroup D z).subtype)
    (hfD : f ∈ D) (hfS : f ∈ S₀) :
    ∃ d e : G, u * f * a = d * e ∧ Commute d e ∧ d ∈ centSet D z ∧ ¬ Commute d w ∧
      e ∈ localGroup D z ∧ Commute e w ∧ ∀ s ∈ D ∩ (S₀ : Set G), Commute e s := by
  classical
  let core : ClassInCore D u w v z S₀ :=
    ClassInCore.ofBender hS htri hn hn1 hord hzdef htrans hB huS hvS hbS
  let base : ClassInBase D u w v z S₀ :=
    ClassInBase.ofCore hS htri hn hord hzdef huS hvS hbS core
  let setup : ClassInSetup D u w v z n S₀ :=
    ClassInSetup.ofBase htri hn hn1 hord hzdef huS hvS hbS base
  have hf₀ : f ∈ D ∩ (S₀ : Set G) := ⟨hfD, hfS⟩
  let fX : setup.base.core.X := ⟨f, setup.base.core.hLX f hf₀⟩
  have hfE : fX ∈ setup.base.core.EX := setup.base.core.hmemX f hf₀
  have hfT : fX ∈ setup.T := setup.hLT f hf₀
  have ha₀ : a ∈ D ∩ (S₀ : Set G) := ⟨haD, haS⟩
  have haX : a ∈ setup.base.core.X := setup.base.core.hLX a ha₀
  let aX : setup.base.core.X := ⟨a, setup.base.core.hLX a ha₀⟩
  have haE : aX ∈ setup.base.core.EX := setup.base.core.hmemX a ha₀
  have huXE : setup.base.core.uX =
      (⟨u, setup.base.core.hLX u ⟨htri.1, huS⟩⟩ : setup.base.core.X) :=
    Subtype.ext setup.base.core.huX
  have huE : setup.base.core.uX ∈ setup.base.core.EX := by
    rw [huXE]
    exact setup.base.core.hmemX u ⟨htri.1, huS⟩
  have huT : setup.base.core.uX ∈ setup.T := by
    rw [huXE]
    exact setup.hLT u ⟨htri.1, huS⟩
  have hxX : a * u⁻¹ ∈ setup.base.core.X :=
    setup.base.core.X.mul_mem haX
      (setup.base.core.X.inv_mem (setup.base.core.hLX u ⟨htri.1, huS⟩))
  have he'a : aX * setup.base.core.uX⁻¹ ∈ CFSG.pCore 2 setup.base.core.X := by
    obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp
      (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 setup.base.core.hXK ⟨hxX, hau⟩)
    have heqX : aX * setup.base.core.uX⁻¹ = q := Subtype.ext (by
      change a * u⁻¹ = (q : G)
      exact hqx.symm)
    rw [heqX]
    exact hq
  obtain ⟨-, hmain⟩ := setup.hKH.main
  obtain ⟨⟨p1, p2⟩, ⟨hp1E, hp2, heq'⟩, -⟩ :=
    hmain setup.base.core.uX ⟨huE, huT⟩ fX ⟨hfE, hfT⟩ aX haE he'a
  exact ClassInSetup.exists_mul_eq_of_eq_mul setup htri.1 huS haD haS hfD hfS hp1E hp2 heq'

theorem exists_commute_of_thirdKind_conj_pCore (hS : Setup G D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n) {z : G} (hzdef : (u * v * w) ^ n = z)
    (htrans : ∀ x ∈ centSet D z, ∃ k ∈ localGroup D z, k * u * k⁻¹ = x)
    (hB : CFSG.BenderSuzuki.IsBenderGroup
      (localGroup D z ⧸ CFSG.solvableRadical (localGroup D z)))
    {q : localGroup D z} (hq : q ∈ CFSG.pCore 2 (localGroup D z)) {a c : G}
    (hadef : (q : G) * u * (q : G)⁻¹ = a) (htriqa : IsTriangle D u c a) {m : ℕ} (hm : Odd m)
    (hordqa : orderOf (u * a * c) = 2 * m) {t : G} (htdef : (u * a * c) ^ m = t)
    (htransqa : ∀ x ∈ centSet D t, ∃ k ∈ localGroup D t, k * u * k⁻¹ = x) :
    ∃ r ∈ D, Commute r u ∧ Commute r v ∧ Commute r w := by
  classical
  have hD := hS.oddT
  obtain ⟨huC, -, -, -⟩ := thirdKind_mem_centSet hS htri hn hord
  rw [hzdef] at huC
  have hu : u ∈ D := htri.1; have hv : v ∈ D := htri.2.1
  have hw : w ∈ D := htri.2.2.1
  obtain ⟨S₀, huS, hvS, hbS, ha₀, _⟩ :=
    exists_sylow_of_thirdKind_conj hS htri hn hord hzdef hq hadef
  have haD : a ∈ D := ha₀.1
  have haS : a ∈ S₀ := ha₀.2
  obtain ⟨g, t', c', hgu', hga', hgt', hgc', htri'c', hord'c', htdef'c', huatS⟩ :=
    exists_conj_involution_thirdKind hS htriqa hm hordqa htdef huS haS
  have htrans't' : ∀ x ∈ centSet D t', ∃ k ∈ localGroup D t', k * u * k⁻¹ = x := by
    have h := transitive_conj_of_conj_eq hS hgu' htransqa
    rwa [hgt'] at h
  have haumemK : a * u⁻¹ ∈ (CFSG.pCore 2 (localGroup D z)).map
      (localGroup D z).subtype :=
    conj_mul_inv_mem_pCore (D := D) (z := z) (mem_localGroup_of_mem huC) hq hadef
  obtain ⟨d, e, hprod, hcomm, hdCz, hdnc, heK, hew, hes⟩ :=
    exists_mul_eq_of_mem_sylow_of_bender hS htri hn hn1 hord hzdef htrans hB
      huS hvS hbS haD haS haumemK huatS.1 huatS.2
  have hta' : Commute t' a := by
    have h := (IsTriangle.third_kind hD hS.normal htri'c' hm hord'c').2.2.2.1
    rwa [htdef'c'] at h
  have hprod_t : u * (u * a * t') * a = t' := by
    calc u * (u * a * t') * a = (u * u) * a * t' * a := by group
      _ = a * t' * a := by rw [hS.oddT.mul_self_eq_one hu, one_mul]
      _ = t' * (a * a) := by
        rw [hta'.symm.eq]
        group
      _ = t' := by rw [hS.oddT.mul_self_eq_one haD, mul_one]
  have ht'de : t' = d * e := by
    rw [← hprod_t, hprod]
  have hdC_t' : d ∈ centSet D t' :=
    ⟨hdCz.1, by rw [ht'de]; exact (Commute.refl d).mul_right hcomm⟩
  obtain ⟨y, hyK, hyu⟩ := htrans't' d hdC_t'
  have hyt : Commute y t' := commute_of_mem_localGroup hyK
  obtain ⟨r, hrD, s, hsD, hne_rs, hrs, he_rs⟩ :=
    exists_two_mem_D_mul_of_conj hS htri'c' hm hord'c' htdef'c'
      (x := u) (y := y) (Or.inl rfl) hyt hyu ht'de
  have hcomm_u : Commute u (r * s) := by
    rw [← he_rs]
    exact (hes u ⟨hu, huS⟩).symm
  have hcomm_v : Commute v (r * s) := by
    rw [← he_rs]
    exact (hes v ⟨hv, hvS⟩).symm
  have hcomm_w : Commute w (r * s) := by
    rw [← he_rs]
    exact hew.symm
  have hru : Commute r u :=
    ((hD.commute_mul_iff hrD hsD hu hne_rs hrs).mp hcomm_u).1.symm
  have hrv : Commute r v :=
    ((hD.commute_mul_iff hrD hsD hv hne_rs hrs).mp hcomm_v).1.symm
  have hrw : Commute r w :=
    ((hD.commute_mul_iff hrD hsD hw hne_rs hrs).mp hcomm_w).1.symm
  exact ⟨r, hrD, hru, hrv, hrw⟩

end Certificates

end CFSG.OddTranspositions
