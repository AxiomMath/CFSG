module

public import CFSG.RankThree.PartOne.S12.Sec1511Y2Quot
public import CFSG.RankThree.PartOne.S12.Sec15FA
public import CFSG.RankThree.PartOne.CTP.OutEmbed
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.ABGLocalTools StrongP

namespace Sec1511

namespace L225

variable {H : Type} [Group H]

structure Setting (S : Subgroup H) [S.Normal] (Ω : Type) [MulAction H Ω] : Prop where
  faithful : ∀ g : H, (∀ x : Ω, g • x = x) → g = 1
  card_Ω : Nat.card Ω = 26
  card_S : Nat.card S = 7800
  trans : ∀ x y : Ω, ∃ s ∈ S, s • x = y
  coatom : ∀ (x : Ω) (Z : Subgroup H), Z ≤ S → S ⊓ MulAction.stabilizer H x ≤ Z →
    Z = S ⊓ MulAction.stabilizer H x ∨ Z = S
  solv : ∀ x : Ω, Group.IsSolvable ↥(S ⊓ MulAction.stabilizer H x)
  fix5 : ∀ a ∈ S, orderOf a = 5 → ∃! x : Ω, a • x = x
  fix3 : ∀ a ∈ S, a ≠ 1 → ∀ x y z : Ω, x ≠ y → x ≠ z → y ≠ z →
    a • x = x → a • y = y → a • z = z → False
  card_H : Nat.card H ∣ 31200
  quot : Group.IsSolvable (H ⧸ S)

structure Syl (S P : Subgroup H) : Prop where
  le : P ≤ S
  card : Nat.card P = 25
  comm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x
  exp : ∀ x ∈ P, x ^ 5 = 1

def IsInfty {Ω : Type} [MulAction H Ω] (P : Subgroup H) (ω₀ : Ω) : Prop :=
  ∀ a ∈ P, a ≠ 1 → ∀ x : Ω, a • x = x ↔ x = ω₀

section Pieces

variable {S P : Subgroup H} {Ω : Type} [MulAction H Ω]

theorem Syl.orderOf_eq (hP : Syl S P) {a : H} (ha : a ∈ P) (ha1 : a ≠ 1) : orderOf a = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (hP.exp a ha) ha1

theorem Syl.exists_ne_one (hP : Syl S P) : ∃ a ∈ P, a ≠ 1 := by
  by_contra h
  have h' : ∀ a ∈ P, a = 1 := fun a ha => by_contra fun h1 => h ⟨a, ha, h1⟩
  have hbot : P = ⊥ := (Subgroup.eq_bot_iff_forall P).2 h'
  have h1 := hP.card
  rw [hbot, Subgroup.card_bot] at h1
  omega

theorem IsInfty.fix {P : Subgroup H} {ω₀ : Ω} (h : IsInfty P ω₀) : ∀ u ∈ P, u • ω₀ = ω₀ := by
  intro u hu
  by_cases hu1 : u = 1
  · rw [hu1, one_smul]
  · exact (h u hu hu1 ω₀).2 rfl

variable [S.Normal]

theorem Setting.exists_ne (hS : Setting S Ω) (ω₀ : Ω) : ∃ x : Ω, x ≠ ω₀ := by
  have : Finite Ω := Nat.finite_of_card_ne_zero (by rw [hS.card_Ω]; norm_num)
  have h1 : 1 < Nat.card Ω := by rw [hS.card_Ω]; norm_num
  have : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.1 h1
  exact _root_.exists_ne ω₀

theorem exists_isInfty (hS : Setting S Ω) (hP : Syl S P) : ∃ ω₀ : Ω, IsInfty P ω₀ := by
  obtain ⟨a₀, ha₀P, ha₀1⟩ := hP.exists_ne_one
  obtain ⟨ω₀, hω₀, huniq⟩ := hS.fix5 a₀ (hP.le ha₀P) (hP.orderOf_eq ha₀P ha₀1)
  have hfix : ∀ a ∈ P, a • ω₀ = ω₀ := by
    intro a ha
    apply huniq
    show a₀ • (a • ω₀) = a • ω₀
    rw [← mul_smul, hP.comm a₀ ha₀P a ha, mul_smul, hω₀]
  refine ⟨ω₀, fun a ha ha1 x => ⟨fun hx => ?_, fun hx => hx ▸ hfix a ha⟩⟩
  obtain ⟨y, -, hyu⟩ := hS.fix5 a (hP.le ha) (hP.orderOf_eq ha ha1)
  exact (hyu x hx).trans (hyu ω₀ (hfix a ha)).symm

theorem exists_translate (hS : Setting S Ω) (hP : Syl S P) {ω₀ : Ω} (hω : IsInfty P ω₀) :
    ∀ x y : Ω, x ≠ ω₀ → y ≠ ω₀ → ∃ u ∈ P, u • x = y := by
  intro x y hx hy
  have hne : ∀ u ∈ P, u • x ≠ ω₀ := by
    intro u hu h
    apply hx
    have h1 : u • x = u • ω₀ := by rw [h, hω.fix u hu]
    exact MulAction.injective u h1
  let f : P → {z : Ω // z ≠ ω₀} := fun u => ⟨(u : H) • x, hne u u.2⟩
  have hinj : Function.Injective f := by
    intro u v huv
    have h1 : (u : H) • x = (v : H) • x := congrArg Subtype.val huv
    have h2 : ((v : H)⁻¹ * u) • x = x := by rw [mul_smul, h1, inv_smul_smul]
    by_contra hne'
    have hvu : (v : H)⁻¹ * u ≠ 1 := by
      intro h
      apply hne'
      exact Subtype.ext (inv_mul_eq_one.1 h).symm
    exact hx ((hω ((v : H)⁻¹ * u) (P.mul_mem (P.inv_mem v.2) u.2) hvu x).1 h2)
  have : Finite Ω := Nat.finite_of_card_ne_zero (by rw [hS.card_Ω]; norm_num)
  have hcard : Nat.card {z : Ω // z ≠ ω₀} = 25 := by
    classical
    have : Fintype Ω := Fintype.ofFinite Ω
    have h1 : Fintype.card Ω = 26 := by rw [← Nat.card_eq_fintype_card]; exact hS.card_Ω
    have h2 : Nat.card {z : Ω // z ≠ ω₀} = Fintype.card Ω - 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    omega
  have hbij := hinj.bijective_of_nat_card_le (by rw [hcard, hP.card])
  obtain ⟨u, hu⟩ := hbij.2 ⟨y, hy⟩
  exact ⟨u, u.2, congrArg Subtype.val hu⟩

theorem fix_of_comm {ω₀ : Ω} (hω : IsInfty P ω₀) {a : H} (haP : a ∈ P) (ha1 : a ≠ 1)
    {c : H} (hc : c * a = a * c) : c • ω₀ = ω₀ := by
  apply (hω a haP ha1 (c • ω₀)).1
  calc a • (c • ω₀) = (a * c) • ω₀ := (mul_smul a c ω₀).symm
    _ = (c * a) • ω₀ := by rw [hc]
    _ = c • (a • ω₀) := mul_smul c a ω₀
    _ = c • ω₀ := by rw [hω.fix a haP]

theorem centralizer_le (hS : Setting S Ω) (hP : Syl S P) {ω₀ : Ω} (hω : IsInfty P ω₀) (c : H)
    (hc : ∀ u ∈ P, c * u = u * c) : c ∈ P := by
  obtain ⟨a, haP, ha1⟩ := hP.exists_ne_one
  have hcinf : c • ω₀ = ω₀ := fix_of_comm hω haP ha1 (hc a haP)
  obtain ⟨x₀, hx₀⟩ := hS.exists_ne ω₀
  have hcx₀ : c • x₀ ≠ ω₀ := fun h => hx₀ (MulAction.injective c (h.trans hcinf.symm))
  obtain ⟨u, huP, hu⟩ := exists_translate hS hP hω x₀ (c • x₀) hx₀ hcx₀
  have hall : ∀ y : Ω, (u⁻¹ * c) • y = y := by
    intro y
    by_cases hy : y = ω₀
    · subst hy
      rw [mul_smul, hcinf, hω.fix u⁻¹ (P.inv_mem huP)]
    · obtain ⟨v, hvP, hv⟩ := exists_translate hS hP hω x₀ y hx₀ hy
      calc (u⁻¹ * c) • y = (u⁻¹ * c) • (v • x₀) := by rw [hv]
        _ = u⁻¹ • ((c * v) • x₀) := by simp only [mul_smul]
        _ = u⁻¹ • ((v * c) • x₀) := by rw [hc v hvP]
        _ = u⁻¹ • (v • (u • x₀)) := by rw [mul_smul, hu]
        _ = u⁻¹ • ((v * u) • x₀) := by rw [mul_smul]
        _ = u⁻¹ • ((u * v) • x₀) := by rw [hP.comm v hvP u huP]
        _ = (u⁻¹ * (u * v)) • x₀ := by simp only [mul_smul]
        _ = v • x₀ := by rw [inv_mul_cancel_left]
        _ = y := hv
  have h1 : u⁻¹ * c = 1 := hS.faithful _ hall
  rw [← inv_mul_eq_one.1 h1]
  exact huP

theorem centralizer_S_le (hS : Setting S Ω) (hP : Syl S P) {ω₀ : Ω} (hω : IsInfty P ω₀) {a : H}
    (haP : a ∈ P) (ha1 : a ≠ 1) {c : H} (hcS : c ∈ S) (hc : c * a = a * c) : c ∈ P := by
  have hcinf : c • ω₀ = ω₀ := fix_of_comm hω haP ha1 hc
  obtain ⟨x₀, hx₀⟩ := hS.exists_ne ω₀
  have hcx₀ : c • x₀ ≠ ω₀ := fun h => hx₀ (MulAction.injective c (h.trans hcinf.symm))
  obtain ⟨u, huP, hu⟩ := exists_translate hS hP hω x₀ (c • x₀) hx₀ hcx₀
  by_contra hcP
  have ht1 : u⁻¹ * c ≠ 1 := by
    intro h
    apply hcP
    rw [← inv_mul_eq_one.1 h]
    exact huP
  have htS : u⁻¹ * c ∈ S := S.mul_mem (S.inv_mem (hP.le huP)) hcS
  have h1 : (u⁻¹ * c) • ω₀ = ω₀ := by rw [mul_smul, hcinf, hω.fix u⁻¹ (P.inv_mem huP)]
  have h2 : (u⁻¹ * c) • x₀ = x₀ := by rw [mul_smul, ← hu, inv_smul_smul]
  have hcomm : (u⁻¹ * c) * a = a * (u⁻¹ * c) := by
    calc u⁻¹ * c * a = u⁻¹ * (c * a) := mul_assoc _ _ _
      _ = u⁻¹ * (a * c) := by rw [hc]
      _ = (u⁻¹ * a) * c := (mul_assoc _ _ _).symm
      _ = (a * u⁻¹) * c := by rw [hP.comm u⁻¹ (P.inv_mem huP) a haP]
      _ = a * (u⁻¹ * c) := mul_assoc _ _ _
  have h3 : (u⁻¹ * c) • (a • x₀) = a • x₀ := by
    rw [← mul_smul, hcomm, mul_smul, h2]
  have hax₀ : a • x₀ ≠ x₀ := fun h => hx₀ ((hω a haP ha1 x₀).1 h)
  have hax₀' : a • x₀ ≠ ω₀ := fun h => hx₀ (by
    have : a • x₀ = a • ω₀ := by rw [h, hω.fix a haP]
    exact MulAction.injective a this)
  exact hS.fix3 (u⁻¹ * c) htS ht1 ω₀ x₀ (a • x₀) hx₀.symm hax₀'.symm hax₀.symm h1 h2 h3

theorem card_stab (hS : Setting S Ω) (ω₀ : Ω) :
    Nat.card ↥(S ⊓ MulAction.stabilizer H ω₀) = 300 := by
  have : MulAction.IsPretransitive ↥S Ω := ⟨fun x y => by
    obtain ⟨s, hs, h⟩ := hS.trans x y
    exact ⟨⟨s, hs⟩, h⟩⟩
  have h1 := MulAction.index_stabilizer_of_transitive (↥S) ω₀
  have h2 := Subgroup.card_mul_index (MulAction.stabilizer (↥S) ω₀)
  rw [h1, hS.card_Ω, hS.card_S] at h2
  have h3 : Nat.card ↥(MulAction.stabilizer (↥S) ω₀) = 300 := by omega
  rw [← h3]
  refine Nat.card_congr
    { toFun := fun h => ⟨⟨h.1, (Subgroup.mem_inf.1 h.2).1⟩, (Subgroup.mem_inf.1 h.2).2⟩
      invFun := fun s => ⟨(s.1 : H), Subgroup.mem_inf.2 ⟨s.1.2, s.2⟩⟩
      left_inv := fun h => rfl
      right_inv := fun s => rfl }

theorem conj_stab_le [Finite H] (hS : Setting S Ω) (hP : Syl S P) {ω₀ : Ω} (hω : IsInfty P ω₀) {g : H}
    (hgS : g ∈ S) (hg : g • ω₀ = ω₀) : ∀ v ∈ P, g * v * g⁻¹ ∈ P := by
  by_contra hcon
  push Not at hcon
  obtain ⟨v₁, hv₁, hv₁'⟩ := hcon
  have hcl : ∀ a ∈ P, g⁻¹ * a * g ∈ P → a = 1 := by
    intro a haP hb
    by_contra ha1
    apply hv₁'
    refine centralizer_S_le hS hP hω haP ha1
      (S.mul_mem (S.mul_mem hgS (hP.le hv₁)) (S.inv_mem hgS)) ?_
    have hb' := hP.comm v₁ hv₁ (g⁻¹ * a * g) hb
    calc g * v₁ * g⁻¹ * a = g * (v₁ * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * a * g) * v₁) * g⁻¹ := by rw [hb']
      _ = a * (g * v₁ * g⁻¹) := by group
  have hginv : g⁻¹ • ω₀ = ω₀ := by rw [inv_smul_eq_iff, hg]
  have hmem : ∀ u v : P, (u : H) * (g * (v : H) * g⁻¹) ∈ S ⊓ MulAction.stabilizer H ω₀ := by
    intro u v
    refine Subgroup.mem_inf.2 ⟨S.mul_mem (hP.le u.2)
      (S.mul_mem (S.mul_mem hgS (hP.le v.2)) (S.inv_mem hgS)), ?_⟩
    rw [MulAction.mem_stabilizer_iff]
    calc ((u : H) * (g * (v : H) * g⁻¹)) • ω₀
        = (u : H) • (g • ((v : H) • (g⁻¹ • ω₀))) := by simp only [mul_smul]
      _ = ω₀ := by rw [hginv, hω.fix v v.2, hg, hω.fix u u.2]
  let φ : P × P → ↥(S ⊓ MulAction.stabilizer H ω₀) := fun p => ⟨(p.1 : H) * (g * (p.2 : H) * g⁻¹), hmem p.1 p.2⟩
  have hφ : Function.Injective φ := by
    intro p q hpq
    have h1 : (p.1 : H) * (g * (p.2 : H) * g⁻¹) = (q.1 : H) * (g * (q.2 : H) * g⁻¹) :=
      congrArg Subtype.val hpq
    have h2 : (q.1 : H)⁻¹ * (p.1 : H) = g * ((q.2 : H) * (p.2 : H)⁻¹) * g⁻¹ := by
      calc (q.1 : H)⁻¹ * (p.1 : H)
          = (q.1 : H)⁻¹ * ((p.1 : H) * (g * (p.2 : H) * g⁻¹)) * (g * (p.2 : H) * g⁻¹)⁻¹ := by group
        _ = (q.1 : H)⁻¹ * ((q.1 : H) * (g * (q.2 : H) * g⁻¹)) * (g * (p.2 : H) * g⁻¹)⁻¹ := by
          rw [h1]
        _ = g * ((q.2 : H) * (p.2 : H)⁻¹) * g⁻¹ := by group
    have h3 : (q.1 : H)⁻¹ * (p.1 : H) = 1 := by
      apply hcl _ (P.mul_mem (P.inv_mem q.1.2) p.1.2)
      rw [h2]
      have : g⁻¹ * (g * ((q.2 : H) * (p.2 : H)⁻¹) * g⁻¹) * g = (q.2 : H) * (p.2 : H)⁻¹ := by group
      rw [this]
      exact P.mul_mem q.2.2 (P.inv_mem p.2.2)
    have hp1 : (p.1 : H) = q.1 := (inv_mul_eq_one.1 h3).symm
    have hp2 : (p.2 : H) = q.2 := by
      rw [hp1] at h1
      have h4 : (g * (p.2 : H) * g⁻¹) = (g * (q.2 : H) * g⁻¹) := mul_left_cancel h1
      calc (p.2 : H) = g⁻¹ * (g * (p.2 : H) * g⁻¹) * g := by group
        _ = g⁻¹ * (g * (q.2 : H) * g⁻¹) * g := by rw [h4]
        _ = q.2 := by group
    exact Prod.ext (Subtype.ext hp1) (Subtype.ext hp2)
  have hcard := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod, hP.card, card_stab hS ω₀] at hcard
  omega

theorem mem_normalizer_of_stab [Finite H] (hS : Setting S Ω) (hP : Syl S P) {ω₀ : Ω} (hω : IsInfty P ω₀)
    {g : H} (hgS : g ∈ S) (hg : g • ω₀ = ω₀) : g ∈ Subgroup.normalizer (P : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => conj_stab_le hS hP hω hgS hg n hn, fun hn => ?_⟩
  have := conj_stab_le hS hP hω (S.inv_mem hgS) (by rw [inv_smul_eq_iff, hg]) _ hn
  have e : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
  rwa [e] at this

theorem not_dvd_quot [Finite H] (hS : Setting S Ω) : ¬ 5 ∣ Nat.card (H ⧸ S) := by
  have h1 := S.card_mul_index
  rw [hS.card_S] at h1
  have h2 := hS.card_H
  rw [← h1] at h2
  have h3 : S.index ∣ 4 := by
    have : 7800 * S.index ∣ 7800 * 4 := by simpa using h2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  intro h5
  have h6 : 5 ∣ S.index := by rwa [← Subgroup.index_eq_card] at h5
  have := h6.trans h3
  omega

omit [S.Normal] in
theorem Syl.of_conj (hP : Syl S P) {P' : Subgroup H} (hle : P' ≤ S) {g : H}
    (hg : ∀ x, x ∈ P' ↔ g⁻¹ * x * g ∈ P) : Syl S P' where
  le := hle
  card := by
    rw [← hP.card]
    refine Nat.card_congr
      { toFun := fun x => ⟨g⁻¹ * (x : H) * g, (hg x).1 x.2⟩
        invFun := fun y => ⟨g * (y : H) * g⁻¹, (hg _).2 (by
          have : g⁻¹ * (g * (y : H) * g⁻¹) * g = y := by group
          rw [this]
          exact y.2)⟩
        left_inv := fun x => Subtype.ext (by group)
        right_inv := fun y => Subtype.ext (by group) }
  comm := fun x hx y hy => by
    have h := hP.comm _ ((hg x).1 hx) _ ((hg y).1 hy)
    have e1 : g⁻¹ * x * g * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g := by group
    have e2 : g⁻¹ * y * g * (g⁻¹ * x * g) = g⁻¹ * (y * x) * g := by group
    rw [e1, e2] at h
    exact mul_left_cancel (mul_right_cancel h)
  exp := fun x hx => by
    have h := hP.exp _ ((hg x).1 hx)
    have e : (g⁻¹ * x * g) ^ 5 = g⁻¹ * x ^ 5 * g := by
      have := conj_pow (a := g⁻¹) (b := x) (i := 5)
      simpa using this
    rw [e] at h
    have h' : x ^ 5 = 1 := by
      have : x ^ 5 = g * (g⁻¹ * x ^ 5 * g) * g⁻¹ := by group
      rw [this, h]
      group
    exact h'

theorem two_subgroup [Finite H] (hS : Setting S Ω) (hP : Syl S P) {ω₀ : Ω} (hω : IsInfty P ω₀)
    (V : Subgroup H) (hV : IsPGroup 2 V) (hPV : P ≤ Subgroup.normalizer (V : Set H)) : V = ⊥ := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVP : ∀ x ∈ V, x ∈ P → x = 1 := by
    intro x hxV hxP
    obtain ⟨k, hk⟩ := hV ⟨x, hxV⟩
    have hk' : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h5 := hP.exp x hxP
    have := pow_gcd_eq_one.2 ⟨hk', h5⟩
    have hg : Nat.gcd (2 ^ k) 5 = 1 := Nat.Coprime.pow_left k (by norm_num)
    rwa [hg, pow_one] at this
  have hSn : ∀ u n : H, u * n * u⁻¹ ∈ S ↔ n ∈ S := fun u n =>
    ⟨fun h => by simpa [mul_assoc] using (inferInstance : S.Normal).conj_mem _ h u⁻¹,
      fun h => (inferInstance : S.Normal).conj_mem n h u⟩
  have hV₀2 : IsPGroup 2 ↥(V ⊓ S) := hV.to_le inf_le_left
  have hcompl : ¬ 5 ∣ Nat.card ↥(V ⊓ S) := by
    obtain ⟨n, hn⟩ := hV₀2.exists_card_eq
    rw [hn]
    intro h5
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h5
    omega
  have hnorm : P ≤ Subgroup.normalizer ((V ⊓ S : Subgroup H) : Set H) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have h1 := Subgroup.mem_normalizer_iff.1 (hPV hu) n
    simp only [Subgroup.mem_inf]
    rw [h1, hSn u n]
  have hpow : ∀ member : ↥P, member ^ 5 = 1 := fun m => Subtype.ext (by simpa using hP.exp m m.2)
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 5
    (by norm_num) P (V ⊓ S) hpow (by rw [hP.card]; norm_num) hcompl hnorm
  have hV₀bot : V ⊓ S = ⊥ := by
    rw [hgen]
    refine iSup_eq_bot.2 fun m => iSup_eq_bot.2 fun hm => ?_
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    obtain ⟨hxV₀, hxC⟩ := Subgroup.mem_inf.1 hx
    have hxS : x ∈ S := (Subgroup.mem_inf.1 hxV₀).2
    have hxV : x ∈ V := (Subgroup.mem_inf.1 hxV₀).1
    have hm1 : (m : H) ≠ 1 := fun h => hm (Subtype.ext h)
    have hcomm : x * (m : H) = (m : H) * x :=
      (Subgroup.mem_centralizer_iff.1 hxC (m : H) (Set.mem_singleton _)).symm
    exact hVP x hxV (centralizer_S_le hS hP hω m.2 hm1 hxS hcomm)
  have hVC : ∀ v ∈ V, ∀ u ∈ P, v * u = u * v := by
    intro v hv u hu
    have hw : v * u * v⁻¹ * u⁻¹ ∈ V ⊓ S := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have h1 : u * v⁻¹ * u⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.1 (hPV hu) v⁻¹).1 (V.inv_mem hv)
        have := V.mul_mem hv h1
        simpa [mul_assoc] using this
      · exact S.mul_mem ((hSn v u).2 (hP.le hu)) (S.inv_mem (hP.le hu))
    rw [hV₀bot] at hw
    exact commutatorElement_eq_one_iff_mul_comm.1 (Subgroup.mem_bot.1 hw)
  refine (Subgroup.eq_bot_iff_forall V).2 fun v hv => ?_
  exact hVP v hv (centralizer_le hS hP hω v fun u hu => (hVC v hv u hu))

theorem exists_order_three [Finite H] (hS : Setting S Ω) (hP : Syl S P) {ω₀ : Ω}
    (hω : IsInfty P ω₀) : ∃ g ∈ Subgroup.normalizer (P : Set H), OrderModC P g 3 := by
  have h3 : 3 ∣ Nat.card ↥(S ⊓ MulAction.stabilizer H ω₀) := by rw [card_stab hS ω₀]; norm_num
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(S ⊓ MulAction.stabilizer H ω₀)) 3 h3
  have hgord : orderOf (x : H) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  have hgS : (x : H) ∈ S := (Subgroup.mem_inf.1 x.2).1
  have hgω : (x : H) • ω₀ = ω₀ := MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 x.2).2
  refine ⟨(x : H), mem_normalizer_of_stab hS hP hω hgS hgω, by norm_num, ?_, ?_⟩
  · have : (x : H) ^ 3 = 1 := by rw [← hgord]; exact pow_orderOf_eq_one _
    rw [this]
    exact Subgroup.one_mem _
  · intro k hk0 hk3 hkC
    have hkP : (x : H) ^ k ∈ P :=
      centralizer_le hS hP hω _ fun u hu => ((Subgroup.mem_centralizer_iff.1 hkC) u hu).symm
    have h5 := hP.exp _ hkP
    have h3' : ((x : H) ^ k) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ← hgord, pow_orderOf_eq_one, one_pow]
    have := pow_gcd_eq_one.2 ⟨h5, h3'⟩
    have hg : Nat.gcd 5 3 = 1 := by norm_num
    rw [hg, pow_one] at this
    have := orderOf_dvd_of_pow_eq_one this
    rw [hgord] at this
    have := Nat.le_of_dvd hk0 this
    omega

theorem solvable_of_spe [Finite H] (hS : Setting S Ω) {P : Subgroup H} (hPs : IsSylowOf 5 P ⊤)
    (hP : Syl S P) {Y₀ : Subgroup H} (hY : IsStronglyPEmbedded 5 Y₀) : Group.IsSolvable ↥Y₀ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P', hP's, hP'Y⟩ := hY.exists_isSylowOf_le
  obtain ⟨g, -, hg⟩ := Sec15FA.exists_conj_of_isSylowOf (by norm_num : Nat.Prime 5) hPs hP's
  have hP'S : P' ≤ S := CTP.le_of_isPGroup_of_not_dvd_card_quotient hP's.2.1 (not_dvd_quot hS)
  have hP' : Syl S P' := hP.of_conj hP'S hg
  obtain ⟨ω', hω'⟩ := exists_isInfty hS hP'
  have hP'1 : P' ≠ ⊥ := by
    intro h
    have h1 := hP'.card
    rw [h, Subgroup.card_bot] at h1
    omega
  have hNY : Subgroup.normalizer (P' : Set H) ≤ Y₀ := hY.normalizer_le hP'1 hP's.2.1 hP'Y
  have hsub : S ⊓ MulAction.stabilizer H ω' ≤ S ⊓ Y₀ := by
    intro x hx
    obtain ⟨hxS, hxω⟩ := Subgroup.mem_inf.1 hx
    exact Subgroup.mem_inf.2 ⟨hxS, hNY (mem_normalizer_of_stab hS hP' hω' hxS
      (MulAction.mem_stabilizer_iff.1 hxω))⟩
  rcases hS.coatom ω' (S ⊓ Y₀) inf_le_left hsub with hZ | hZ
  · have hsolv : Group.IsSolvable ↥(S ⊓ Y₀) := by rw [hZ]; exact hS.solv ω'
    have := hS.quot
    refine Group.isSolvable_of_ker_le_range
      (Subgroup.inclusion (inf_le_right : S ⊓ Y₀ ≤ Y₀)) ((QuotientGroup.mk' S).comp Y₀.subtype) ?_
    intro y hy
    have hyS : (y : H) ∈ S := (QuotientGroup.eq_one_iff (y : H)).1 hy
    exact ⟨⟨y, Subgroup.mem_inf.2 ⟨hyS, y.2⟩⟩, rfl⟩
  · exfalso
    have hSY : S ≤ Y₀ := by
      rw [← hZ]
      exact inf_le_right
    exact hY.not_dvd_card_of_normal_le hSY (by rw [hS.card_S]; norm_num)

theorem kfL225_of_setting [Finite H] (hS : Setting S Ω) :
    ∀ Y₀ : Subgroup H, IsStronglyPEmbedded 5 Y₀ →
      ∀ P : Subgroup H, IsSylowOf 5 P ⊤ → IsElementaryAbelian 5 (omegaOne 5 P) →
        Nat.card (omegaOne 5 P) = 25 →
        Nat.card P = 25 ∧
        (∀ V : Subgroup H, IsPGroup 2 V →
          omegaOne 5 P ≤ Subgroup.normalizer (V : Set H) → V = ⊥) ∧
        Group.IsSolvable ↥Y₀ ∧
        ∃ g ∈ Subgroup.normalizer ((omegaOne 5 P : Subgroup H) : Set H),
          OrderModC (omegaOne 5 P) g 3 := by
  intro Y₀ hY P hPs hPel hPcard
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcardP : Nat.card P = 25 := by
    obtain ⟨k, hk⟩ := hPs.2.1.exists_card_eq
    have hle : omegaOne 5 P ≤ P := (Subgroup.closure_le _).2 fun x hx => hx.1
    have h25 : 25 ≤ Nat.card P := hPcard ▸ Subgroup.card_le_of_le hle
    have hdvd : 5 ^ k ∣ 31200 := hk ▸ (Subgroup.card_subgroup_dvd_card P).trans hS.card_H
    have hk2 : k ≤ 2 := by
      by_contra hk3
      have h125 : 5 ^ 3 ∣ 5 ^ k := pow_dvd_pow 5 (by omega)
      have := h125.trans hdvd
      norm_num at this
    rw [hk] at h25 ⊢
    interval_cases k <;> simp_all
  have hle : omegaOne 5 P ≤ P := (Subgroup.closure_le _).2 fun x hx => hx.1
  have hΩ : omegaOne 5 P = P := Subgroup.eq_of_le_of_card_ge hle (by rw [hcardP, hPcard])
  have hPS : P ≤ S := CTP.le_of_isPGroup_of_not_dvd_card_quotient hPs.2.1 (not_dvd_quot hS)
  have hP : Syl S P := by
    have := hPel
    refine ⟨hPS, hcardP, fun x hx y hy => ?_, fun x hx => ?_⟩
    · have hx' : x ∈ omegaOne 5 P := by rw [hΩ]; exact hx
      have hy' : y ∈ omegaOne 5 P := by rw [hΩ]; exact hy
      exact congrArg Subtype.val
        (IsMulCommutative.is_comm.comm (⟨x, hx'⟩ : ↥(omegaOne 5 P)) ⟨y, hy'⟩)
    · have hx' : x ∈ omegaOne 5 P := by rw [hΩ]; exact hx
      exact elemPow_eq_one_of_isElementaryAbelian (p := 5) (A := omegaOne 5 P) x hx'
  obtain ⟨ω₀, hω⟩ := exists_isInfty hS hP
  refine ⟨hcardP, ?_, solvable_of_spe hS hPs hP hY, ?_⟩
  · intro V hV hPV
    rw [hΩ] at hPV
    exact two_subgroup hS hP hω V hV hPV
  · rw [hΩ]
    exact exists_order_three hS hP hω

end Pieces

end L225

end Sec1511

end CFSG.RankThree.PartOne
