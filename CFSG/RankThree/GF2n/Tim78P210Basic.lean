module

public import CFSG.RankThree.GF2n.Tim78Abelian
public import CFSG.RankThree.GF2n.Tim77Prop24Core
public import CFSG.RankThree.PartTwo.Sec5.Hyp
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalTightCommuting

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.CGT.Timmesfeld75
open CFSG.ComponentClassification.LiteratureLocal.TightCommuting
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type*} [Group G]

theorem mem_omegaOneSub_iff {B : Subgroup G} (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) {x : G} :
    x ∈ PartTwo.omegaOneSub B ↔ x ∈ B ∧ x * x = 1 := by
  let I : Subgroup ↥B :=
    { carrier := {y | y ^ 2 = 1}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        have hab : a * b = b * a := Subtype.ext (hB a a.2 b b.2)
        show (a * b) ^ 2 = 1
        rw [(Commute.mul_pow hab 2), ha, hb, one_mul]
      inv_mem' := fun {a} ha => by
        show a⁻¹ ^ 2 = 1
        rw [inv_pow, ha, inv_one] }
  have hω : CFSG.omega₁ ↥B (p := 2) = I := by
    have h : CFSG.omega₁ ↥B (p := 2) = Subgroup.closure {y : ↥B | y ^ 2 = 1} := by
      simp only [CFSG.omega₁, CFSG.omega, pow_one]
    rw [h]
    exact le_antisymm ((Subgroup.closure_le _).mpr fun y hy => hy)
      fun y hy => Subgroup.subset_closure hy
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [hω] at hy
    refine ⟨y.2, ?_⟩
    have : (y ^ 2 : ↥B) = 1 := hy
    have h2 := congrArg Subtype.val this
    rw [Subgroup.coe_pow, sq] at h2
    exact h2
  · rintro ⟨hxB, hx⟩
    refine ⟨⟨x, hxB⟩, ?_, rfl⟩
    rw [hω]
    show (⟨x, hxB⟩ : ↥B) ^ 2 = 1
    exact Subtype.ext (by rw [Subgroup.coe_pow, sq]; exact hx)

theorem omegaOneSub_conj {B : Subgroup G} (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (g : G) :
    PartTwo.omegaOneSub (conjSubgroup g B) = conjSubgroup g (PartTwo.omegaOneSub B) := by
  have hB' : ∀ x ∈ conjSubgroup g B, ∀ y ∈ conjSubgroup g B, x * y = y * x := by
    intro x hx y hy
    have h := hB _ (mem_conjSubgroup.mp hx) _ (mem_conjSubgroup.mp hy)
    calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = y * x := by group
  ext x
  rw [mem_omegaOneSub_iff hB', mem_conjSubgroup, mem_conjSubgroup, mem_omegaOneSub_iff hB]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [show g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g by group, h2]
    group
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    calc x * x = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = 1 := by rw [h2, mul_one, mul_inv_cancel]

theorem rightConjugate_inv_eq (B : Subgroup G) (g : G) :
    rightConjugate B g⁻¹ = conjSubgroup g B := by
  ext x
  rw [mem_rightConjugate_iff, mem_conjSubgroup, inv_inv]

variable [Finite G]

theorem commute_of_le_normalizer {B : Subgroup G} (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hB2 : IsPGroup 2 B) (hB1 : B ≠ ⊥) (hTI : IsTI B) {g : G}
    (hle : conjSubgroup g B ≤ Subgroup.normalizer (B : Set G)) :
    ∀ a ∈ B, ∀ b ∈ conjSubgroup g B, a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hne : conjSubgroup g B = B
  · rw [hne]
    exact hBc
  have h2' : IsPGroup 2 (conjSubgroup g B) := by
    have := hB2.map (MulAut.conj g).toMonoidHom
    exact this
  have hS2 : IsPGroup 2 (B ⊔ conjSubgroup g B : Subgroup G) := by
    rw [sup_comm]
    exact IsPGroup.to_sup_of_normal_right' h2' hB2 hle
  have htight : TightlyEmbedded B := by
    refine ⟨?_, fun h hh => ?_⟩
    · obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hB2
      rw [hk]
      rcases k with _ | k
      · exact absurd (Subgroup.eq_bot_of_card_eq B (by simpa using hk)) hB1
      · exact (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero k⟩)
    · rw [show rightConjugate B h = conjSubgroup h⁻¹ B by
        rw [← rightConjugate_inv_eq, inv_inv]]
      rcases hTI h⁻¹ with h0 | h0
      · rw [h0, Subgroup.card_bot]
        exact odd_one
      · exfalso
        apply hh
        have hle' : B ≤ conjSubgroup h⁻¹ B := h0.symm.le.trans inf_le_right
        have heq : conjSubgroup h⁻¹ B = B := (Subgroup.eq_of_le_of_card_ge hle'
          (card_conjSubgroup h⁻¹ B).le).symm
        have := conjSubgroup_eq_self_iff.mp heq
        simpa using (Subgroup.normalizer _).inv_mem this
  have hs : Setup B ⊤ B (B ⊔ conjSubgroup g B) :=
    { tight := htight
      le_inf := le_inf le_top le_rfl
      sylow := fun R hR _ hBR => le_antisymm (hR.trans inf_le_right) hBR
      pGroup := hB2
      ne_bot := hB1
      S_le := le_top
      S_pGroup := hS2
      le_S := le_sup_left }
  obtain ⟨hc, -⟩ := hs.commutes_of_le_normalizer (Subgroup.mem_top g⁻¹)
    (by rw [rightConjugate_inv_eq]; exact hne) (by rw [rightConjugate_inv_eq]; exact le_sup_right)
    (by rw [rightConjugate_inv_eq]; exact hle)
  rw [rightConjugate_inv_eq] at hc
  exact hc

theorem exists_ne_one_commute' {U : Subgroup G} (hU : IsPGroup 2 U) (hU1 : U ≠ ⊥) {w : G}
    (hw : ∃ k : ℕ, w ^ 2 ^ k = 1) (hwN : w ∈ Subgroup.normalizer (U : Set G)) :
    ∃ u ∈ U, u ≠ 1 ∧ w * u = u * w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : IsPGroup 2 (Subgroup.zpowers w) := by
    obtain ⟨k, hk⟩ := hw
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hKN : Subgroup.zpowers w ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.zpowers_le).mpr hwN
  set K := Subgroup.zpowers w ⊔ U with hKdef
  have hKp : IsPGroup 2 K := hK.to_sup_of_normal_right' hU hKN
  have hUK : U ≤ K := le_sup_right
  have hnorm : (U.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hUK]
    intro h k hh hk
    exact (Subgroup.mem_normalizer_iff.1 ((sup_le hKN Subgroup.le_normalizer) hk) h).1 hh
  have hnil : Group.IsNilpotent K := hKp.isNilpotent
  have hne' : U.subgroupOf K ≠ ⊥ := by
    intro h
    apply hU1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hUK hx⟩ : K) ∈ U.subgroupOf K := hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  obtain ⟨⟨z, hz⟩, hz1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one.1 (Group.IsNilpotent.inf_center_ne_bot_of_normal hne'))
  refine ⟨z.1, hz.1, fun h => hz1 (Subtype.ext (Subtype.ext h)), ?_⟩
  have hc := Subgroup.mem_center_iff.1 hz.2 ⟨w, (le_sup_left : Subgroup.zpowers w ≤ K)
    (Subgroup.mem_zpowers w)⟩
  exact congrArg Subtype.val hc

structure Setup210 (B₀ B₁ : Subgroup G) : Prop where
  comm : ∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x
  two : IsPGroup 2 B₀
  exp_ne : ∃ x ∈ B₀, x ^ 2 ≠ 1
  ti : IsTI B₀
  conj : ∃ g : G, B₁ = conjSubgroup g B₀
  ne_bot : B₀ ⊓ Subgroup.normalizer (B₁ : Set G) ≠ ⊥

namespace Setup210

variable {B₀ B₁ : Subgroup G} (S : Setup210 B₀ B₁)
include S

omit [Finite G] in
theorem isPGroup : IsPGroup 2 B₀ := S.two

omit [Finite G] in
theorem pow_two_pow_eq_one {x : G} (hx : x ∈ B₀) : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := S.two ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

omit [Finite G] in
theorem ne_bot' : B₀ ≠ ⊥ := fun h => S.ne_bot (by rw [h, bot_inf_eq])

omit [Finite G] in
theorem comm₁ : ∀ x ∈ B₁, ∀ y ∈ B₁, x * y = y * x := by
  obtain ⟨g, rfl⟩ := S.conj
  intro x hx y hy
  have h := S.comm _ (mem_conjSubgroup.mp hx) _ (mem_conjSubgroup.mp hy)
  calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
    _ = y * x := by group

omit [Finite G] in
theorem two₁ : IsPGroup 2 B₁ := by
  obtain ⟨g, rfl⟩ := S.conj
  exact S.two.map (MulAut.conj g).toMonoidHom

omit [Finite G] in
theorem exp_ne₁ : ∃ x ∈ B₁, x ^ 2 ≠ 1 := by
  obtain ⟨g, rfl⟩ := S.conj
  obtain ⟨x, hx, hx2⟩ := S.exp_ne
  refine ⟨g * x * g⁻¹, ?_, fun h => hx2 ?_⟩
  · rw [mem_conjSubgroup, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
    exact hx
  · rw [conj_pow] at h
    calc x ^ 2 = g⁻¹ * (g * x ^ 2 * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group

omit [Finite G] in
theorem ti₁ : IsTI B₁ := by
  obtain ⟨g, rfl⟩ := S.conj
  exact isTI_conjSubgroup S.ti g

omit [Finite G] in
theorem isPGroup₁ : IsPGroup 2 B₁ := S.two₁

theorem inf_eq_bot (hne : B₀ ≠ B₁) : B₀ ⊓ B₁ = ⊥ := by
  obtain ⟨g, rfl⟩ := S.conj
  exact inf_conjSubgroup_eq_bot_of_isTI S.ti (Ne.symm hne)

theorem mem_normalizer_of_commute {c x : G} (hx : x ∈ B₀) (hx1 : x ≠ 1) (hcx : c * x = x * c) :
    c ∈ Subgroup.normalizer (B₀ : Set G) :=
  Tim77.mem_normalizer_of_commute_of_isTI S.ti hx hx1 hcx

theorem mem_normalizer_of_commute₁ {c x : G} (hx : x ∈ B₁) (hx1 : x ≠ 1) (hcx : c * x = x * c) :
    c ∈ Subgroup.normalizer (B₁ : Set G) :=
  Tim77.mem_normalizer_of_commute_of_isTI S.ti₁ hx hx1 hcx

theorem commutes_of_sq_ne_one {x : G} (hx : x ∈ B₀ ⊓ Subgroup.normalizer (B₁ : Set G))
    (hx2 : x * x ≠ 1) : ∀ a ∈ B₀, ∀ b ∈ B₁, a * b = b * a := by
  obtain ⟨hxB, hxN⟩ := Subgroup.mem_inf.mp hx
  by_cases hne : B₀ = B₁
  · subst hne
    exact S.comm
  have hinf := S.inf_eq_bot hne
  have hx1 : x ≠ 1 := fun h => hx2 (by rw [h, one_mul])
  have hsq : x ^ 2 = x * x := sq x
  have hC : B₁ ⊓ Subgroup.centralizer ({x} : Set G) =
      B₁ ⊓ Subgroup.centralizer ({x ^ 2} : Set G) := by
    apply le_antisymm
    · intro c hc
      obtain ⟨hcB, hcC⟩ := Subgroup.mem_inf.mp hc
      rw [Subgroup.mem_centralizer_singleton_iff] at hcC
      refine Subgroup.mem_inf.mpr ⟨hcB, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, hsq]
      calc c * (x * x) = (c * x) * x := by group
        _ = (x * c) * x := by rw [hcC]
        _ = x * (c * x) := by group
        _ = x * (x * c) := by rw [hcC]
        _ = x * x * c := by group
    · intro c hc
      obtain ⟨hcB, hcC⟩ := Subgroup.mem_inf.mp hc
      rw [Subgroup.mem_centralizer_singleton_iff, hsq] at hcC
      refine Subgroup.mem_inf.mpr ⟨hcB, ?_⟩
      have hcN : c ∈ Subgroup.normalizer (B₀ : Set G) :=
        S.mem_normalizer_of_commute (B₀.mul_mem hxB hxB) hx2 hcC
      have h1 : x * c * x⁻¹ * c⁻¹ ∈ B₁ :=
        B₁.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN c).mp hcB) (B₁.inv_mem hcB)
      have h2 : x * c * x⁻¹ * c⁻¹ ∈ B₀ := by
        rw [mul_assoc, mul_assoc]
        refine B₀.mul_mem hxB ?_
        have := (Subgroup.mem_normalizer_iff.mp hcN x⁻¹).mp (B₀.inv_mem hxB)
        rwa [← mul_assoc]
      have h3 : x * c * x⁻¹ * c⁻¹ ∈ B₀ ⊓ B₁ := Subgroup.mem_inf.mpr ⟨h2, h1⟩
      rw [hinf, Subgroup.mem_bot] at h3
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc c * x = (x * c * x⁻¹ * c⁻¹)⁻¹ * (x * c) := by group
        _ = x * c := by rw [h3, inv_one, one_mul]
  have hcen := tim78_2_1 (S := B₁) ⟨⟨fun a b => Subtype.ext (S.comm₁ a a.2 b b.2)⟩⟩ S.isPGroup₁
    hxN (S.pow_two_pow_eq_one hxB) hC
  have hB₁N : B₁ ≤ Subgroup.normalizer (B₀ : Set G) := fun b hb => by
    have := hcen hb
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact S.mem_normalizer_of_commute hxB hx1 this
  obtain ⟨g, hg⟩ := S.conj
  rw [hg] at hB₁N ⊢
  exact commute_of_le_normalizer S.comm S.isPGroup S.ne_bot' S.ti hB₁N

theorem ne_bot₁ : B₁ ⊓ Subgroup.normalizer (B₀ : Set G) ≠ ⊥ := by
  obtain ⟨⟨x, hx⟩, hx1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp S.ne_bot
  have hx1 : x ≠ 1 := fun h => hx1' (Subtype.ext h)
  obtain ⟨hxB, hxN⟩ := Subgroup.mem_inf.mp hx
  have hB₁1 : B₁ ≠ ⊥ := by
    obtain ⟨g, rfl⟩ := S.conj
    intro h
    apply S.ne_bot'
    rw [eq_bot_iff]
    intro y hy
    have : g * y * g⁻¹ ∈ conjSubgroup g B₀ := by
      rw [mem_conjSubgroup, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
      exact hy
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot, show y = g⁻¹ * (g * y * g⁻¹) * g by group, this]
    group
  obtain ⟨b, hb, hb1, hxb⟩ := exists_ne_one_commute' S.isPGroup₁ hB₁1
    (S.pow_two_pow_eq_one hxB) hxN
  intro h
  have : b ∈ B₁ ⊓ Subgroup.normalizer (B₀ : Set G) :=
    Subgroup.mem_inf.mpr ⟨hb, S.mem_normalizer_of_commute hxB hx1 hxb.symm⟩
  rw [h, Subgroup.mem_bot] at this
  exact hb1 this

theorem symm : Setup210 B₁ B₀ where
  comm := S.comm₁
  two := S.two₁
  exp_ne := S.exp_ne₁
  ti := S.ti₁
  conj := by
    obtain ⟨g, hg⟩ := S.conj
    exact ⟨g⁻¹, by rw [hg, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]⟩
  ne_bot := S.ne_bot₁

end Setup210

end CFSG.RankThree.GF2n.Tim78
