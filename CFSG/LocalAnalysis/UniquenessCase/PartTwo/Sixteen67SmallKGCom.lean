module

public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open CFSG.Open Subgroup

theorem s1667_kg_conjNormal_injective {Q : Type} [Group Q] (J : Subgroup Q) [J.Normal]
    (hC : centralizer (J : Set Q) = ⊥) :
    Function.Injective (MulAut.conjNormal : Q →* MulAut ↥J) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  have hcomm : q ∈ centralizer (J : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have h2 : q * j * q⁻¹ = j := by
      have hh : ((MulAut.conjNormal q ⟨j, hj⟩ : ↥J) : Q) = ((1 : MulAut ↥J) ⟨j, hj⟩ : Q) :=
        congrArg (fun y : ↥J => (y : Q)) (DFunLike.congr_fun hq ⟨j, hj⟩)
      rw [MulAut.conjNormal_apply q ⟨j, hj⟩] at hh
      simpa [MulAut.one_apply] using hh
    have h3 : q * j = j * q := by
      have hh : (q * j * q⁻¹) * q = j * q := congrArg (· * q) h2
      simpa [mul_assoc] using hh
    exact h3.symm
  exact Subgroup.mem_bot.mp (hC ▸ hcomm)

theorem s1667_kg_mem_iff_conjNormal_mem_range {Q : Type} [Group Q] (J : Subgroup Q) [J.Normal]
    (hC : centralizer (J : Set Q) = ⊥) (q : Q) :
    q ∈ J ↔ (MulAut.conjNormal q : MulAut ↥J) ∈ (MulAut.conj : ↥J →* MulAut ↥J).range := by
  constructor
  · intro hq
    exact MonoidHom.mem_range.mpr ⟨⟨q, hq⟩, (MulAut.conjNormal_val (H := J) (h := ⟨q, hq⟩)).symm⟩
  · intro hq
    obtain ⟨j, hj⟩ := MonoidHom.mem_range.mp hq
    have hqj : (j : Q) = q :=
      s1667_kg_conjNormal_injective J hC (by rw [MulAut.conjNormal_val, hj])
    rw [← hqj]
    exact j.2

theorem s1667_kg_mem_normalizer_zpowers_of_inv {Q : Type} [Group Q] {x s : Q}
    (hsx : s * x * s⁻¹ = x⁻¹) : s ∈ normalizer ((zpowers x : Subgroup Q) : Set Q) := by
  have h1 : s * x⁻¹ * s⁻¹ = x := by
    have := congrArg (·⁻¹) hsx
    simpa [mul_assoc] using this
  have hinv : s⁻¹ * x * s = x⁻¹ := by
    calc s⁻¹ * x * s = s⁻¹ * (s * x⁻¹ * s⁻¹) * s := by rw [h1]
      _ = x⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hh
    refine mem_zpowers_iff.mpr ⟨-n, ?_⟩
    rw [← hn, ← conj_zpow, hsx, zpow_neg, ← inv_zpow]
  · intro hh
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hh
    refine mem_zpowers_iff.mpr ⟨-n, ?_⟩
    have h3 : h = s⁻¹ * (s * h * s⁻¹) * s := by group
    have h2 : s⁻¹ * x ^ n * s = (s⁻¹ * x * s) ^ n := by
      have := conj_zpow (a := s⁻¹) (b := x) (i := n)
      simpa using this.symm
    rw [h3, ← hn, h2, hinv, inv_zpow, zpow_neg]

theorem s1667_kg_mem_normalizer_zpowers_of_mem_centralizer {Q : Type} [Group Q] {x t : Q}
    (ht : t ∈ centralizer ({x} : Set Q)) : t ∈ normalizer ((zpowers x : Subgroup Q) : Set Q) := by
  have h : t ∈ centralizer ((zpowers x : Subgroup Q) : Set Q) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact ht
  exact Subgroup.centralizer_le_normalizer _ h

theorem s1667_kg_four_dvd_card {Q : Type} [Group Q] [Finite Q] {A : Subgroup Q}
    (hA : IsElemAbelian 2 A) (h4 : 4 ≤ Nat.card A) : 4 ∣ Nat.card A := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x x.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  rw [hn] at h4 ⊢
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have h1 : n ≤ 1 := by omega
    have h2 : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
    omega
  refine ⟨2 ^ (n - 2), ?_⟩
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
  congr 1
  omega

theorem s1667_kg_card_le_two_of_le_cyclic {Q : Type} [Group Q] [Finite Q] {Z B : Subgroup Q}
    (hZ : IsCyclic ↥Z) (hB : B ≤ Z) (hE : IsElemAbelian 2 B) : Nat.card B ≤ 2 := by
  haveI : IsCyclic (B.subgroupOf Z) := Subgroup.isCyclic _
  haveI : IsCyclic ↥B :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hB).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hB).surjective
  obtain ⟨b, hb⟩ := IsCyclic.exists_generator (α := ↥B)
  have hb2 : b ^ 2 = 1 := Subtype.ext (by simpa using hE.2 (b : Q) b.2)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hb]
  exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hb2)

theorem s1667_kg_exists_generator {Q : Type} [Group Q] {T : Subgroup Q} (hT : IsCyclic ↥T) :
    ∃ g ∈ T, ∀ t ∈ T, t ∈ zpowers g := by
  obtain ⟨g, hg⟩ := hT.exists_generator
  refine ⟨g, g.2, fun t ht => ?_⟩
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hg ⟨t, ht⟩)
  exact mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩

theorem s1667_kg_sq_comm_of_cyclic {Q : Type} [Group Q] (J : Subgroup Q) [J.Normal] {x g : Q}
    (hgJ : g ∈ J) (hgx : g ∈ centralizer ({x} : Set Q))
    (hT : ∀ t ∈ J ⊓ centralizer ({x} : Set Q), t ∈ zpowers g) {B : Subgroup Q}
    (hB : IsElemAbelian 2 B) (hBx : B ≤ centralizer ({x} : Set Q))
    (hgn : g ∈ normalizer (B : Set Q)) {b : Q} (hb : b ∈ B) : g ^ 2 * b = b * g ^ 2 := by
  have hgb : g * b * g⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hgn b).mp hb
  set c : Q := g * b * g⁻¹ * b⁻¹ with hc
  have hcB : c ∈ B := B.mul_mem hgb (B.inv_mem hb)
  have hcJ : c ∈ J := by
    have h1 : b * g⁻¹ * b⁻¹ ∈ J := ‹J.Normal›.conj_mem g⁻¹ (J.inv_mem hgJ) b
    have h2 : c = g * (b * g⁻¹ * b⁻¹) := by rw [hc]; group
    rw [h2]
    exact J.mul_mem hgJ h1
  have hgx' : Commute g x := Subgroup.mem_centralizer_singleton_iff.mp hgx
  have hbx' : Commute b x := Subgroup.mem_centralizer_singleton_iff.mp (hBx hb)
  have hcx' : Commute c x :=
    (((hgx'.mul_left hbx').mul_left hgx'.inv_left).mul_left hbx'.inv_left)
  have hcT : c ∈ zpowers g := hT c ⟨hcJ, Subgroup.mem_centralizer_singleton_iff.mpr hcx'⟩
  have hcg : g * c = c * g := by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hcT
    rw [← hn]
    exact ((Commute.refl g).zpow_right n).eq
  have hc2 : c * c = 1 := by
    have := hB.2 c hcB
    rwa [pow_two] at this
  have h1 : g * b * g⁻¹ = c * b := by rw [hc]; group
  have h2 : g * c * g⁻¹ = c := by rw [hcg]; group
  have h3 : g * (g * b * g⁻¹) * g⁻¹ = b := by
    rw [h1]
    calc g * (c * b) * g⁻¹ = (g * c * g⁻¹) * (g * b * g⁻¹) := by group
      _ = c * (c * b) := by rw [h2, h1]
      _ = b := by rw [← mul_assoc, hc2, one_mul]
  rw [pow_two]
  calc g * g * b = g * (g * b * g⁻¹) * g⁻¹ * (g * g) := by group
    _ = b * (g * g) := by rw [h3]

theorem s1667_kg_exists_not_comm {Q : Type} [Group Q] {x s : Q} {E : Subgroup Q}
    (hx3 : orderOf x = 3) (hsx : s * x * s⁻¹ = x⁻¹) (hxn : x ∈ normalizer (E : Set Q))
    (hEx : E ⊓ centralizer ({x} : Set Q) = ⊥) (hE1 : E ≠ ⊥) : ∃ e ∈ E, s * e ≠ e * s := by
  by_contra hcon
  have hcom : ∀ e ∈ E, s * e = e * s := fun e he =>
    not_not.1 fun h => hcon ⟨e, he, h⟩
  have hx3' : x * x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx3] at h
    simpa [pow_succ, mul_assoc] using h
  have hx1 : x * x * (x * x) = x := by
    calc x * x * (x * x) = x * (x * x * x) := by group
      _ = x := by rw [hx3', mul_one]
  have hcen : ∀ e ∈ E, e * x = x * e := by
    intro e he
    have hxe : x * e * x⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hxn e).mp he
    have hse : s * e * s⁻¹ = e := by rw [hcom e he]; group
    have hy : s * (x * e * x⁻¹) * s⁻¹ = x * e * x⁻¹ := by rw [hcom _ hxe]; group
    have hy' : s * (x * e * x⁻¹) * s⁻¹ = x⁻¹ * e * x := by
      calc s * (x * e * x⁻¹) * s⁻¹ = (s * x * s⁻¹) * (s * e * s⁻¹) * (s * x⁻¹ * s⁻¹) := by group
        _ = x⁻¹ * e * x := by
          rw [hsx, hse, show s * x⁻¹ * s⁻¹ = (s * x * s⁻¹)⁻¹ by group, hsx]
          group
    have h4 : x * x * e = e * (x * x) := by
      calc x * x * e = x * (x * e * x⁻¹) * x := by group
        _ = x * (x⁻¹ * e * x) * x := by rw [hy.symm.trans hy']
        _ = e * (x * x) := by group
    calc e * x = e * (x * x * (x * x)) := by rw [hx1]
      _ = (e * (x * x)) * (x * x) := by group
      _ = (x * x * e) * (x * x) := by rw [h4]
      _ = x * x * (e * (x * x)) := by group
      _ = x * x * (x * x * e) := by rw [h4]
      _ = x * e := by
        calc x * x * (x * x * e) = (x * x * (x * x)) * e := by group
          _ = x * e := by rw [hx1]
  apply hE1
  rw [eq_bot_iff]
  intro e he
  have hec : e ∈ centralizer ({x} : Set Q) := Subgroup.mem_centralizer_singleton_iff.mpr (hcen e he)
  have hmem : e ∈ E ⊓ centralizer ({x} : Set Q) := ⟨he, hec⟩
  rw [hEx, Subgroup.mem_bot] at hmem
  rw [hmem]
  exact Subgroup.one_mem _

theorem s1667_kg_false_of_inverting_two_element {Q : Type} [Group Q] [Finite Q] {J : Subgroup Q}
    (hab : ∀ P : Subgroup Q, P ≤ J → IsPGroup 2 P → ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    {x s : Q} (hx3 : orderOf x = 3) (hs2 : ∃ k : ℕ, orderOf s = 2 ^ k) (hsJ : s ∈ J)
    (hsx : s * x * s⁻¹ = x⁻¹) {E : Subgroup Q} (hE4 : Nat.card E = 4) (hEJ : E ≤ J)
    (hEx : E ⊓ centralizer ({x} : Set Q) = ⊥) (hxn : x ∈ normalizer (E : Set Q))
    (hsn : s ∈ normalizer (E : Set Q)) : False := by
  have hE1 : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE4
    exact absurd hE4 (by norm_num)
  obtain ⟨e, heE, hne⟩ := s1667_kg_exists_not_comm hx3 hsx hxn hEx hE1
  have hsp : IsPGroup 2 (zpowers s) := by
    obtain ⟨k, hk⟩ := hs2
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hEp : IsPGroup 2 E := IsPGroup.of_card (n := 2) (by rw [hE4]; norm_num)
  have hP : IsPGroup 2 ↥(zpowers s ⊔ E) :=
    IsPGroup.to_sup_of_normal_right' hsp hEp (Subgroup.zpowers_le.mpr hsn)
  exact hne (hab (zpowers s ⊔ E) (sup_le (Subgroup.zpowers_le.mpr hsJ) hEJ) hP s
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers s)) e (Subgroup.mem_sup_right heE))

theorem s1667_kg_false_of_inverting_involution {Q : Type} [Group Q] [Finite Q] {J : Subgroup Q}
    (hab : ∀ P : Subgroup Q, P ≤ J → IsPGroup 2 P → ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    {x s : Q} (hx3 : orderOf x = 3) (hs2 : s ^ 2 = 1) (hsJ : s ∈ J) (hsx : s * x * s⁻¹ = x⁻¹)
    {E : Subgroup Q} (hE4 : Nat.card E = 4) (hEJ : E ≤ J)
    (hEx : E ⊓ centralizer ({x} : Set Q) = ⊥) (hxn : x ∈ normalizer (E : Set Q))
    (hsn : s ∈ normalizer (E : Set Q)) : False := by
  have hd : orderOf s ∣ 2 := orderOf_dvd_of_pow_eq_one hs2
  have hk : ∃ k : ℕ, orderOf s = 2 ^ k := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact ⟨0, by rw [h]; rfl⟩
    · exact ⟨1, by rw [h]; rfl⟩
  exact s1667_kg_false_of_inverting_two_element hab hx3 hk hsJ hsx hE4 hEJ hEx hxn hsn

theorem s1667_kg_exists_two_element_inverting {Q : Type} [Group Q] [Finite Q] {x w : Q}
    (hw : w * x * w⁻¹ = x⁻¹) :
    ∃ s : Q, s ∈ zpowers w ∧ s * x * s⁻¹ = x⁻¹ ∧ ∃ k : ℕ, orderOf s = 2 ^ k := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos w).ne'
  have hmpos : 0 < m := hm.pos
  have hw2 : w ^ 2 * x = x * w ^ 2 := by
    have h1 : w * x⁻¹ * w⁻¹ = x := by
      have := congrArg (·⁻¹) hw
      simpa [mul_assoc] using this
    rw [pow_two]
    calc w * w * x = w * (w * x * w⁻¹) * w := by group
      _ = w * x⁻¹ * w := by rw [hw]
      _ = (w * x⁻¹ * w⁻¹) * (w * w) := by group
      _ = x * (w * w) := by rw [h1]
  have hcomm : Commute (w ^ 2) x := hw2
  obtain ⟨r, hr⟩ := hm
  have hs : w ^ m * x * (w ^ m)⁻¹ = x⁻¹ := by
    have hcr : (w ^ 2) ^ r * x⁻¹ = x⁻¹ * (w ^ 2) ^ r := ((hcomm.pow_left r).inv_right).eq
    have hexp : w ^ m = (w ^ 2) ^ r * w := by rw [hr, pow_succ, pow_mul]
    rw [hexp]
    generalize (w ^ 2) ^ r = u at hcr ⊢
    calc u * w * x * (u * w)⁻¹ = u * (w * x * w⁻¹) * u⁻¹ := by group
      _ = u * x⁻¹ * u⁻¹ := by rw [hw]
      _ = x⁻¹ := by rw [hcr]; group
  refine ⟨w ^ m, ⟨m, by simp⟩, hs, k, ?_⟩
  rw [orderOf_pow' w hmpos.ne', hn, Nat.gcd_mul_left_left]
  exact Nat.mul_div_cancel _ hmpos

theorem s1667_kg_comm_of_le {Q : Type} [Group Q] (J : Subgroup Q)
    (hab : ∀ P : Subgroup ↥J, IsPGroup 2 P → ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) :
    ∀ P : Subgroup Q, P ≤ J → IsPGroup 2 P → ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  intro P hPJ hP a ha b hb
  have hP' : IsPGroup 2 (P.subgroupOf J) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPJ).symm
  exact congrArg Subtype.val (hab (P.subgroupOf J) hP' ⟨a, hPJ ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
    ⟨b, hPJ hb⟩ (Subgroup.mem_subgroupOf.mpr hb))

theorem s1667_kg_elemAbelian_sup_card_gt {Q : Type} [Group Q] [Finite Q] {E W : Subgroup Q}
    (hE : IsElemAbelian 2 E) (hE4 : Nat.card E = 4) (hW : IsElemAbelian 2 W) (hW1 : W ≠ ⊥)
    (hcomm : ∀ a ∈ E, ∀ b ∈ W, a * b = b * a) (hEW : E ⊓ W = ⊥) :
    IsElemAbelian 2 (E ⊔ W) ∧ 4 < Nat.card ↥(E ⊔ W) := by
  refine ⟨IsElemAbelian.sup_of_commute hE hW hcomm, ?_⟩
  by_contra hle
  have hle' : Nat.card ↥(E ⊔ W) ≤ 4 := not_lt.1 hle
  have heq : E = E ⊔ W := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hE4]; exact hle')
  apply hW1
  rw [eq_bot_iff, ← hEW]
  exact le_inf (heq ▸ le_sup_right) le_rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
