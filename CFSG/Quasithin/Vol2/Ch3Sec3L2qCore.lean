module

public import CFSG.Quasithin.Vol2.Ch3Sec3L2qFacts
public import CFSG.Quasithin.Vol2.Ch3Sec3BenderCore

public section

namespace CFSG.Quasithin.H13.L2qC

open CFSG.GorensteinWalter CFSG.Quasithin.H13.L2q
open CFSG.QuasithinUnique (IsSylowTwoOf)

variable {Q : Type*} [Group Q]

section Proj

variable {A A' : Subgroup Q}

theorem exists_decomp (hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) (x : ↥(A ⊔ A')) :
    ∃ p : ↥A × ↥A', (p.1 : Q) * p.2 = x := by
  obtain ⟨a, ha, b, hb, e⟩ := (BenC.mem_sup_iff hc).mp x.2
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), e.symm⟩

@[expose] noncomputable def proj2 (hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) (hi : A ⊓ A' = ⊥) :
    ↥(A ⊔ A') →* ↥A' where
  toFun x := (Classical.choose (exists_decomp hc x)).2
  map_one' := by
    have h := Classical.choose_spec (exists_decomp hc (1 : ↥(A ⊔ A')))
    set p := Classical.choose (exists_decomp hc (1 : ↥(A ⊔ A')))
    have h1 : (p.1 : Q) * p.2 = 1 * 1 := by rw [h, mul_one]; rfl
    exact Subtype.ext (BenC.eq_of_mul_eq hi p.1.2 A.one_mem p.2.2 A'.one_mem h1).2
  map_mul' x y := by
    have hx := Classical.choose_spec (exists_decomp hc x)
    have hy := Classical.choose_spec (exists_decomp hc y)
    have hxy := Classical.choose_spec (exists_decomp hc (x * y))
    set p := Classical.choose (exists_decomp hc x)
    set r := Classical.choose (exists_decomp hc y)
    set s := Classical.choose (exists_decomp hc (x * y))
    have h1 : (s.1 : Q) * s.2 = ((p.1 : Q) * r.1) * ((p.2 : Q) * r.2) := by
      rw [hxy, Subgroup.coe_mul, ← hx, ← hy]
      have := hc r.1 r.1.2 p.2 p.2.2
      calc (p.1 : Q) * p.2 * (r.1 * r.2) = p.1 * (p.2 * r.1) * r.2 := by group
        _ = p.1 * (r.1 * p.2) * r.2 := by rw [this]
        _ = p.1 * r.1 * (p.2 * r.2) := by group
    exact Subtype.ext (BenC.eq_of_mul_eq hi s.1.2 (A.mul_mem p.1.2 r.1.2) s.2.2
      (A'.mul_mem p.2.2 r.2.2) h1).2

theorem proj2_spec (hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) (hi : A ⊓ A' = ⊥)
    (x : ↥(A ⊔ A')) : ∃ a ∈ A, (x : Q) = a * (proj2 hc hi x : Q) := by
  have h := Classical.choose_spec (exists_decomp hc x)
  exact ⟨_, (Classical.choose (exists_decomp hc x)).1.2, h.symm⟩

theorem inf_ne_bot (hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) (hi : A ⊓ A' = ⊥) {P : Subgroup Q}
    (hP : P ≤ A ⊔ A') (hPc : Nat.card P = 9) (hP3 : ∀ p ∈ P, p ^ 3 = 1)
    (hcyc : ∀ H : Subgroup ↥A', IsPGroup 3 H → IsCyclic H) : P ⊓ A ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hbot
  set f := (proj2 hc hi).comp (Subgroup.inclusion hP) with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro p hp
    obtain ⟨a, ha, he⟩ := proj2_spec hc hi (Subgroup.inclusion hP p)
    have hp' : (proj2 hc hi (Subgroup.inclusion hP p) : Q) = 1 := by
      rw [show proj2 hc hi (Subgroup.inclusion hP p) = f p from rfl, hp]
      rfl
    rw [hp', mul_one] at he
    have hpA : (p : Q) ∈ A := by
      have hpp : (p : Q) = (Subgroup.inclusion hP p : Q) := rfl
      rw [hpp, he]
      exact ha
    have h1 : (p : Q) ∈ P ⊓ A := ⟨p.2, hpA⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hP3g : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hPc]; norm_num)
  have hrc : IsCyclic f.range :=
    hcyc _ (hP3g.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  have : IsCyclic ↥P :=
    (MulEquiv.isCyclic (MonoidHom.ofInjective hinj)).mpr hrc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥P)
  have hg3 : g ^ 3 = 1 := Subtype.ext (hP3 g g.2)
  have := orderOf_le_of_pow_eq_one (by norm_num) hg3
  omega

end Proj

section Conj

variable {A : Subgroup Q} {d : Q}

@[expose] noncomputable def conjRes (hd : d ∈ Subgroup.normalizer (A : Set Q)) : MulAut ↥A where
  toFun a := ⟨d * a * d⁻¹, (Subgroup.mem_normalizer_iff.mp hd a).mp a.2⟩
  invFun a := ⟨d⁻¹ * a * d, by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hd) a).mp a.2
    simpa using this⟩
  left_inv a := by ext; simp [mul_assoc]
  right_inv a := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

theorem conjRes_apply (hd : d ∈ Subgroup.normalizer (A : Set Q)) (a : ↥A) :
    ((conjRes hd a : ↥A) : Q) = d * a * d⁻¹ := rfl

theorem conjRes_pow_apply (hd : d ∈ Subgroup.normalizer (A : Set Q)) (n : ℕ) (a : ↥A) :
    (((conjRes hd ^ n) a : ↥A) : Q) = d ^ n * a * (d ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, conjRes_apply, ih, pow_succ']
    group

theorem orderOf_conjRes_dvd (hd : d ∈ Subgroup.normalizer (A : Set Q)) :
    orderOf (conjRes hd) ∣ orderOf d := by
  apply orderOf_dvd_of_pow_eq_one
  ext a
  rw [conjRes_pow_apply, pow_orderOf_eq_one, one_mul, inv_one, mul_one]
  rfl

end Conj

section Core

variable [Finite Q] {F : Type} [Field F] [Finite F] {q : ℕ} {A A' T Y P D : Subgroup Q}

omit [Finite Q] in
theorem centralizes_of_eight (eA : ↥A ≃* PSL2 F)
    (hF : Nat.card F = q) (hq : q.Prime) (hq5 : 5 ≤ q) (h8 : q % 8 = 1 ∨ q % 8 = 7)
    (hS : IsSylowTwoOf (T ⊓ A) A) {d : Q} (hdA : d ∈ Subgroup.normalizer (A : Set Q))
    (hdT : d ∈ Subgroup.normalizer (T : Set Q)) (hdo : Odd (orderOf d)) :
    ∀ a ∈ A, d * a * d⁻¹ = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α := conjRes hdA with hα
  have hαo : Odd (orderOf α) := Odd.of_dvd_nat hdo (orderOf_conjRes_dvd hdA)
  obtain ⟨x, hxo, hx⟩ := exists_conj_X eA hF hq hq5 α hαo
  set S := (T ⊓ A).subgroupOf A with hSdef
  have hS2 : IsPGroup 2 S := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hSi : ¬ 2 ∣ S.index := hS.2.2
  have hxN : x ∈ Subgroup.normalizer (S : Set ↥A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      rw [← hx s]
      show d * (s : Q) * d⁻¹ ∈ T ⊓ A
      exact ⟨(Subgroup.mem_normalizer_iff.mp hdT s).mp hs.1,
        (Subgroup.mem_normalizer_iff.mp hdA s).mp s.2⟩
    · intro hs
      have h1 : s = α⁻¹ (x * s * x⁻¹) := by
        rw [← hx, MulAut.inv_apply_self]
      rw [h1]
      have h2 : ((α⁻¹ (x * s * x⁻¹) : ↥A) : Q) = d⁻¹ * (x * s * x⁻¹ : ↥A) * d := by
        have : α⁻¹ (x * s * x⁻¹) = ⟨d⁻¹ * ((x * s * x⁻¹ : ↥A) : Q) * d, by
          have := (Subgroup.mem_normalizer_iff.mp (inv_mem hdA) _).mp (x * s * x⁻¹).2
          simpa using this⟩ := by
          apply α.injective
          rw [MulAut.apply_inv_self]
          ext
          rw [conjRes_apply]
          simp [mul_assoc]
        rw [this]
      show ((α⁻¹ (x * s * x⁻¹) : ↥A) : Q) ∈ T ⊓ A
      rw [h2]
      refine ⟨?_, (α⁻¹ (x * s * x⁻¹)).2 |> fun h => by rw [← h2]; exact h⟩
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hdT) _).mp hs.1
      simpa using this
  have hxS : x ∈ S := (normalizer_sylow eA hF hq hq5 h8 hS2 hSi) ▸ hxN
  have hx1 : x = 1 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hS2) ⟨x, hxS⟩
    rw [Subgroup.orderOf_mk] at hk
    rw [hk] at hxo
    rcases k with _ | k
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hk
    · exact absurd hxo (by rw [Nat.not_odd_iff_even]; exact (Nat.even_pow.mpr ⟨even_two,
        Nat.succ_ne_zero k⟩))
  intro a ha
  have := hx ⟨a, ha⟩
  rw [hx1, one_mul, inv_one, mul_one] at this
  exact congrArg Subtype.val this

omit [Finite Q] in
theorem mem_normalizer_subgroupOf {x : ↥A} :
    x ∈ Subgroup.normalizer (((T ⊓ A).subgroupOf A : Subgroup ↥A) : Set ↥A) ↔
      (x : Q) ∈ Subgroup.normalizer ((T ⊓ A : Subgroup Q) : Set Q) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h g
    by_cases hgA : g ∈ A
    · exact h ⟨g, hgA⟩
    · constructor
      · intro hg
        exact absurd hg.2 hgA
      · intro hg
        exfalso
        apply hgA
        have h1 : (x : Q) * g * (x : Q)⁻¹ ∈ A := hg.2
        have : g = (x : Q)⁻¹ * ((x : Q) * g * (x : Q)⁻¹) * x := by group
        rw [this]
        exact A.mul_mem (A.mul_mem (A.inv_mem x.2) h1) x.2
  · intro h g
    exact h g

theorem part_A (eA : ↥A ≃* PSL2 F) (eA' : ↥A' ≃* PSL2 F)
    (hF : Nat.card F = q) (hq : q.Prime) (hq5 : 5 ≤ q) (h3 : q % 8 = 3 ∨ q % 8 = 5)
    (hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) (hi : A ⊓ A' = ⊥) (hS : IsSylowTwoOf (T ⊓ A) A)
    (hT2 : IsPGroup 2 T) (hYA : Y ≤ A ⊔ A') (hTY : T ≤ Subgroup.normalizer (Y : Set Q))
    (hPY : P ≤ Y) (hP9 : Nat.card P = 9) (hY3 : ∀ y ∈ Y, y ^ 3 ∈ T) :
    (q % 24 = 11 ∨ q % 24 = 13) ∨
      ((Y ⊓ A).subgroupOf A =
          Subgroup.normalizer (((T ⊓ A).subgroupOf A : Subgroup ↥A) : Set ↥A) ∧
        Nonempty (↥((Y ⊓ A).subgroupOf A) ≃* alternatingGroup (Fin 4))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP3 : ∀ p ∈ P, p ^ 3 = 1 := by
    intro p hp
    have h9 : p ^ 9 = 1 := by
      have := pow_card_eq_one' (x := (⟨p, hp⟩ : ↥P))
      rw [hP9] at this
      exact congrArg Subtype.val this
    have hT : p ^ 3 ∈ T := hY3 p (hPY hp)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT2) ⟨_, hT⟩
    rw [Subgroup.orderOf_mk] at hk
    have h1 : orderOf (p ^ 3) ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [← pow_mul]; exact h9)
    rw [hk] at h1
    rcases k with _ | k
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hk
    · exfalso
      have : 2 ∣ 3 := (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans h1
      omega
  have hPA : P ⊓ A ≠ ⊥ := inf_ne_bot hc hi (hPY.trans hYA) hP9 hP3
    (fun H h3 => isCyclic_three eA' hF hq hq5 H h3)
  have h3U : 3 ∣ Nat.card ((Y ⊓ A).subgroupOf A) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Y ⊓ A ≤ A)).toEquiv]
    have hP3g : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP9]; norm_num)
    have hPA3 : IsPGroup 3 ↥(P ⊓ A) := hP3g.to_le inf_le_left
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPA3
    have hk1 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hPA (Subgroup.eq_bot_of_card_eq _ hk)
    have h1 : 3 ∣ Nat.card ↥(P ⊓ A) := by
      rw [hk]
      exact dvd_pow_self 3 hk1
    exact h1.trans (Subgroup.card_dvd_of_le (inf_le_inf_right A hPY))
  have hSU : (T ⊓ A).subgroupOf A ≤
      Subgroup.normalizer (((Y ⊓ A).subgroupOf A : Subgroup ↥A) : Set ↥A) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have hsT : (s : Q) ∈ T := hs.1
    constructor
    · intro hu
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hTY hsT) u).mp hu.1,
        A.mul_mem (A.mul_mem s.2 u.2) (A.inv_mem s.2)⟩
    · intro hu
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hTY hsT) u).mpr hu.1, u.2⟩
  have hUo : ∀ u ∈ (Y ⊓ A).subgroupOf A, ∃ k, u ^ (3 * 2 ^ k) = 1 := by
    intro u hu
    have hy3 : (u : Q) ^ 3 ∈ T := hY3 _ hu.1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT2) ⟨_, hy3⟩
    rw [Subgroup.orderOf_mk] at hk
    have h1 : ((u : Q) ^ 3) ^ (2 ^ k) = 1 := by
      rw [← hk]
      exact pow_orderOf_eq_one _
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, pow_mul, h1]
    rfl
  have hS2 : IsPGroup 2 ((T ⊓ A).subgroupOf A) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  exact lemma_U eA hF hq hq5 h3 hS2 hS.2.2 hSU h3U hUo

omit [Finite Q] in
theorem mem_normalizer_inf {d : Q} (hdT : d ∈ Subgroup.normalizer (T : Set Q))
    (hdA : d ∈ Subgroup.normalizer (A : Set Q)) :
    d ∈ Subgroup.normalizer ((T ⊓ A : Subgroup Q) : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact ⟨(Subgroup.mem_normalizer_iff.mp hdT g).mp hg.1,
      (Subgroup.mem_normalizer_iff.mp hdA g).mp hg.2⟩
  · intro hg
    exact ⟨(Subgroup.mem_normalizer_iff.mp hdT g).mpr hg.1,
      (Subgroup.mem_normalizer_iff.mp hdA g).mpr hg.2⟩

omit [Finite Q] in
theorem mem_of_normalizes (eA : ↥A ≃* PSL2 F) (hF : Nat.card F = q)
    (hq : q.Prime) (hq5 : 5 ≤ q) (h3 : q % 8 = 3 ∨ q % 8 = 5) (hS : IsSylowTwoOf (T ⊓ A) A)
    (hU : (Y ⊓ A).subgroupOf A =
      Subgroup.normalizer (((T ⊓ A).subgroupOf A : Subgroup ↥A) : Set ↥A))
    (fA : ↥((Y ⊓ A).subgroupOf A) ≃* alternatingGroup (Fin 4)) {a : Q} (ha : a ∈ A)
    (h1 : ∀ u ∈ Y ⊓ A, a * u * a⁻¹ ∈ Y) (h2 : ∀ u ∈ Y ⊓ A, a⁻¹ * u * a ∈ Y) : a ∈ Y := by
  set U := (Y ⊓ A).subgroupOf A with hUdef
  set S := (T ⊓ A).subgroupOf A with hSdef
  set x : ↥A := ⟨a, ha⟩ with hx
  have hS2 : IsPGroup 2 S := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hS4 : Nat.card S = 4 := card_sylow_four eA hF hq hq5 h3 hS2 hS.2.2
  have hxU : x ∈ Subgroup.normalizer (U : Set ↥A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      exact ⟨h1 u hu, A.mul_mem (A.mul_mem ha u.2) (A.inv_mem ha)⟩
    · intro hu
      have e : u = x⁻¹ * (x * u * x⁻¹) * x := by group
      rw [e]
      exact ⟨h2 _ hu, A.mul_mem (A.mul_mem (A.inv_mem ha) (x * u * x⁻¹).2) ha⟩
  have hSU : S ≤ U := hU ▸ Subgroup.le_normalizer
  set K := S.map (MulAut.conj x).toMonoidHom with hK
  have hKU : K ≤ U := by
    rintro _ ⟨s, hs, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hxU s).mp (hSU hs)
  have hK4 : Nat.card K = 4 :=
    ((Nat.card_congr (S.equivMapOfInjective _ (MulAut.conj x).injective).toEquiv).symm).trans hS4
  have hsub : S.subgroupOf U = K.subgroupOf U :=
    eq_of_card_four_alt4' fA
      ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSU).toEquiv).trans hS4)
      ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKU).toEquiv).trans hK4)
  have hSK : S = K := by
    have h := Subgroup.subgroupOf_inj.mp hsub
    rwa [inf_of_le_left hSU, inf_of_le_left hKU] at h
  have hxS : x ∈ Subgroup.normalizer (S : Set ↥A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      rw [hSK]
      exact ⟨s, hs, rfl⟩
    · intro hs
      rw [hSK] at hs
      obtain ⟨s', hs', e⟩ := hs
      have : s' = s := by
        simpa [MulAut.conj_apply] using e
      exact this ▸ hs'
  have : x ∈ U := hU ▸ hxS
  exact this.1

omit [Finite Q] in
theorem conj_mem_of_eq_normalizer {B : Subgroup Q}
    (hU : (Y ⊓ B).subgroupOf B =
      Subgroup.normalizer (((T ⊓ B).subgroupOf B : Subgroup ↥B) : Set ↥B))
    {d : Q} (hdB : d ∈ Subgroup.normalizer (B : Set Q))
    (hdT : d ∈ Subgroup.normalizer (T : Set Q)) {u : Q} (hu : u ∈ Y ⊓ B) :
    d * u * d⁻¹ ∈ Y ⊓ B := by
  have hdu : d * u * d⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hdB u).mp hu.2
  have hu' : (⟨u, hu.2⟩ : ↥B) ∈
      Subgroup.normalizer (((T ⊓ B).subgroupOf B : Subgroup ↥B) : Set ↥B) := by
    rw [← hU]
    exact Subgroup.mem_subgroupOf.mpr hu
  have hdTB := mem_normalizer_inf hdT hdB
  have h1 : d * u * d⁻¹ ∈ Subgroup.normalizer ((T ⊓ B : Subgroup Q) : Set Q) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hdTB (mem_normalizer_subgroupOf.mp hu'))
      (Subgroup.inv_mem _ hdTB)
  have h2 : (⟨d * u * d⁻¹, hdu⟩ : ↥B) ∈ (Y ⊓ B).subgroupOf B := by
    rw [hU]
    exact mem_normalizer_subgroupOf.mpr h1
  exact Subgroup.mem_subgroupOf.mp h2

theorem le_normalizer_core (eA : ↥A ≃* PSL2 F)
    (eA' : ↥A' ≃* PSL2 F) (hF : Nat.card F = q) (hq : q.Prime) (hq5 : 5 ≤ q)
    (hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) (hi : A ⊓ A' = ⊥) (hS : IsSylowTwoOf (T ⊓ A) A)
    (hS' : IsSylowTwoOf (T ⊓ A') A') (hT2 : IsPGroup 2 T) (hYA : Y ≤ A ⊔ A')
    (hTY : T ≤ Subgroup.normalizer (Y : Set Q)) (hPY : P ≤ Y) (hP9 : Nat.card P = 9)
    (hY3 : ∀ y ∈ Y, y ^ 3 ∈ T) (hDA : D ≤ Subgroup.normalizer (A : Set Q))
    (hDA' : D ≤ Subgroup.normalizer (A' : Set Q)) (hDT : D ≤ Subgroup.normalizer (T : Set Q))
    (hDo : ∀ x ∈ D, Odd (orderOf x)) :
    D ≤ Subgroup.normalizer (Y : Set Q) ∨ q % 24 = 11 ∨ q % 24 = 13 := by
  have hc' : ∀ a ∈ A', ∀ b ∈ A, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hi' : A' ⊓ A = ⊥ := by rw [inf_comm]; exact hi
  have hYA' : Y ≤ A' ⊔ A := by rw [sup_comm]; exact hYA
  have hsuff : (∀ d ∈ D, ∀ y ∈ Y, d * y * d⁻¹ ∈ Y) → D ≤ Subgroup.normalizer (Y : Set Q) := by
    intro key d hd
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key d hd y, fun hy => ?_⟩
    have := key d⁻¹ (D.inv_mem hd) _ hy
    simpa [mul_assoc] using this
  obtain ⟨k, hk⟩ := hq.odd_of_ne_two (by omega)
  rcases (by omega : (q % 8 = 1 ∨ q % 8 = 7) ∨ (q % 8 = 3 ∨ q % 8 = 5)) with h8 | h3
  ·
    refine Or.inl (hsuff fun d hd y hy => ?_)
    obtain ⟨a, ha, b, hb, rfl⟩ := (BenC.mem_sup_iff hc).mp (hYA hy)
    have h1 := centralizes_of_eight eA hF hq hq5 h8 hS (hDA hd) (hDT hd) (hDo d hd) a ha
    have h2 := centralizes_of_eight eA' hF hq hq5 h8 hS' (hDA' hd) (hDT hd) (hDo d hd) b hb
    have e : d * (a * b) * d⁻¹ = (d * a * d⁻¹) * (d * b * d⁻¹) := by group
    rw [e, h1, h2]
    exact hy
  rcases part_A eA eA' hF hq hq5 h3 hc hi hS hT2 hYA hTY hPY hP9 hY3 with h24 | ⟨hU, ⟨fA⟩⟩
  · exact Or.inr h24
  rcases part_A eA' eA hF hq hq5 h3 hc' hi' hS' hT2 hYA' hTY hPY hP9 hY3 with
    h24 | ⟨hU', ⟨fA'⟩⟩
  · exact Or.inr h24
  refine Or.inl (hsuff fun d hd y hy => ?_)
  obtain ⟨a, ha, b, hb, rfl⟩ := (BenC.mem_sup_iff hc).mp (hYA hy)
  have hab : ∀ u ∈ A, (a * b) * u * (a * b)⁻¹ = a * u * a⁻¹ := by
    intro u hu
    have h1 := hc u hu b hb
    calc a * b * u * (a * b)⁻¹ = a * (b * u) * b⁻¹ * a⁻¹ := by group
      _ = a * (u * b) * b⁻¹ * a⁻¹ := by rw [h1]
      _ = a * u * a⁻¹ := by group
  have hab' : ∀ u ∈ A, (a * b)⁻¹ * u * (a * b) = a⁻¹ * u * a := by
    intro u hu
    have h1 := hc _ (A.mul_mem (A.mul_mem (A.inv_mem ha) hu) ha) b hb
    calc (a * b)⁻¹ * u * (a * b) = b⁻¹ * ((a⁻¹ * u * a) * b) := by group
      _ = b⁻¹ * (b * (a⁻¹ * u * a)) := by rw [h1]
      _ = a⁻¹ * u * a := by group
  have haY : a ∈ Y := mem_of_normalizes eA hF hq hq5 h3 hS hU fA ha
    (fun u hu => by
      rw [← hab u hu.2]
      exact Y.mul_mem (Y.mul_mem hy hu.1) (Y.inv_mem hy))
    (fun u hu => by
      rw [← hab' u hu.2]
      exact Y.mul_mem (Y.mul_mem (Y.inv_mem hy) hu.1) hy)
  have hbY : b ∈ Y := by
    have e : b = a⁻¹ * (a * b) := by group
    rw [e]
    exact Y.mul_mem (Y.inv_mem haY) hy
  have e : d * (a * b) * d⁻¹ = (d * a * d⁻¹) * (d * b * d⁻¹) := by group
  rw [e]
  exact Y.mul_mem (conj_mem_of_eq_normalizer hU (hDA hd) (hDT hd) ⟨haY, ha⟩).1
    (conj_mem_of_eq_normalizer hU' (hDA' hd) (hDT hd) ⟨hbY, hb⟩).1

end Core

end CFSG.Quasithin.H13.L2qC
