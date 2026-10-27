module

public import CFSG.RankThree.PartOne.Q1327.Irr

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Q1327 CFSG.RankThree.PartOne.Torsion37
  CFSG.RankThree.PartOne.K1320 CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1327

variable {G : Type} [Group G] {p : ℕ} {E : Subgroup G}

theorem card_autFixed [Finite G] (hd : RefFacts.ElemData p E) (hcard : Nat.card E = p ^ 3)
    {t : MulAut E} (ht : IsAutReflection p E t) : Nat.card (autFixed E t) = p ^ 2 := by
  have hp := hd.prime
  have h := Sec13Base.card_eq_mul hd.comm t
  rw [hcard, ht.2] at h
  have h2 : p ^ 2 * p = Nat.card (autFixed E t) * p := by rw [← pow_succ, ← h]
  exact (Nat.eq_of_mul_eq_mul_right hp.pos h2).symm

theorem exists_fixed_pair [Finite G] (hd : RefFacts.ElemData p E) (hcard : Nat.card E = p ^ 3)
    {t₁ t₂ : MulAut E} (h₁ : IsAutReflection p E t₁) (h₂ : IsAutReflection p E t₂) :
    ∃ a : E, a ≠ 1 ∧ t₁ a = a ∧ t₂ a = a := by
  classical
  have hp := hd.prime
  have c1 := card_autFixed hd hcard h₁
  have c2 := card_autFixed hd hcard h₂
  have i1 : (autFixed E t₁).index = p := by
    have := Subgroup.card_mul_index (autFixed E t₁)
    rw [hcard, c1] at this
    have h3 : p ^ 2 * (autFixed E t₁).index = p ^ 2 * p := by rw [this, ← pow_succ]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) h3
  have i2 : (autFixed E t₂).index = p := by
    have := Subgroup.card_mul_index (autFixed E t₂)
    rw [hcard, c2] at this
    have h3 : p ^ 2 * (autFixed E t₂).index = p ^ 2 * p := by rw [this, ← pow_succ]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) h3
  have hle := Subgroup.index_inf_le (H := autFixed E t₁) (K := autFixed E t₂)
  by_contra hno
  push Not at hno
  have hbot : autFixed E t₁ ⊓ autFixed E t₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    rw [Subgroup.mem_bot]
    by_contra hx
    exact hno x hx hx1 hx2
  rw [hbot, Subgroup.index_bot, i1, i2, hcard] at hle
  have : p ^ 3 ≤ p * p := hle
  have h3 : p * p < p ^ 3 := by
    have := Nat.pow_lt_pow_right hp.one_lt (show 2 < 3 by norm_num)
    simpa [pow_two] using this
  omega

section Norm

variable (hcomm : ∀ a b : E, a * b = b * a)

@[expose] def normMap (t₁ t₂ : MulAut E) : E →* E :=
  letI : CommGroup E := { (inferInstance : Group E) with mul_comm := hcomm }
  MonoidHom.mk' (fun v => v * t₁ v * t₂ v * t₁ (t₂ v) * t₂ (t₁ v) * t₁ (t₂ (t₁ v))) (fun a b => by
    simp only [map_mul]
    ac_rfl)

theorem normMap_apply (t₁ t₂ : MulAut E) (v : E) :
    normMap hcomm t₁ t₂ v = v * t₁ v * t₂ v * t₁ (t₂ v) * t₂ (t₁ v) * t₁ (t₂ (t₁ v)) := rfl

variable {t₁ t₂ : MulAut E} (h11 : t₁ * t₁ = 1) (h22 : t₂ * t₂ = 1) (h3 : (t₁ * t₂) ^ 3 = 1)

include h11 h22 h3 in
theorem relation_three : t₁ * t₂ * t₁ = t₂ * t₁ * t₂ := by
  have hi1 : t₁⁻¹ = t₁ := inv_eq_of_mul_eq_one_right h11
  have hi2 : t₂⁻¹ = t₂ := inv_eq_of_mul_eq_one_right h22
  have h : t₁ * t₂ * t₁ * (t₂ * t₁ * t₂) = 1 := by
    have : (t₁ * t₂) ^ 3 = t₁ * t₂ * t₁ * (t₂ * t₁ * t₂) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [← this]
    exact h3
  have h' := eq_inv_of_mul_eq_one_left h
  rw [h', mul_inv_rev, mul_inv_rev, hi1, hi2]
  group

include hcomm h11 in
theorem normMap_t₁ (v : E) : normMap hcomm t₁ t₂ (t₁ v) = normMap hcomm t₁ t₂ v := by
  have r1 : ∀ x : E, t₁ (t₁ x) = x := fun x => by
    simpa using congrArg (fun m : MulAut E => m x) h11
  let _ : CommGroup E := { (inferInstance : Group E) with mul_comm := hcomm }
  rw [normMap_apply, normMap_apply]
  simp only [r1]
  ac_rfl

include hcomm h11 h22 h3 in
theorem normMap_t₂ (v : E) : normMap hcomm t₁ t₂ (t₂ v) = normMap hcomm t₁ t₂ v := by
  have r2 : ∀ x : E, t₂ (t₂ x) = x := fun x => by
    simpa using congrArg (fun m : MulAut E => m x) h22
  have r3 : ∀ x : E, t₁ (t₂ (t₁ x)) = t₂ (t₁ (t₂ x)) := fun x => by
    have := relation_three h11 h22 h3
    simpa using congrArg (fun m : MulAut E => m x) this
  let _ : CommGroup E := { (inferInstance : Group E) with mul_comm := hcomm }
  have e1 : t₁ (t₂ (t₁ (t₂ v))) = t₂ (t₁ v) := by rw [r3 (t₂ v), r2]
  have e2 : t₂ (t₁ (t₂ v)) = t₁ (t₂ (t₁ v)) := (r3 v).symm
  rw [normMap_apply, normMap_apply, e1, e2]
  simp only [r2]
  ac_rfl

include hcomm in
theorem normMap_fixed {a : E} (h1 : t₁ a = a) (h2 : t₂ a = a) :
    normMap hcomm t₁ t₂ a = a ^ 6 := by
  simp only [normMap_apply, h1, h2]
  simp [pow_succ, mul_assoc]

include hcomm h11 in
theorem normMap_moved_left {x : E} (hx : x ∈ autMoved E t₁) : normMap hcomm t₁ t₂ x = 1 := by
  rw [← Sec13Base.range_moveHom hcomm t₁] at hx
  obtain ⟨e, rfl⟩ := hx
  rw [Sec13Base.moveHom_apply, map_mul, map_inv, normMap_t₁ hcomm h11, mul_inv_cancel]

include hcomm h11 h22 h3 in
theorem normMap_moved_right {x : E} (hx : x ∈ autMoved E t₂) : normMap hcomm t₁ t₂ x = 1 := by
  rw [← Sec13Base.range_moveHom hcomm t₂] at hx
  obtain ⟨e, rfl⟩ := hx
  rw [Sec13Base.moveHom_apply, map_mul, map_inv, normMap_t₂ hcomm h11 h22 h3, mul_inv_cancel]

include hcomm h11 h22 h3 in
theorem fixed_inf_lines (hp : p.Prime) (hp5 : 5 ≤ p) (hpow : ∀ a : E, a ^ p = 1) {a : E}
    (h1 : t₁ a = a) (h2 : t₂ a = a) (ha : a ∈ autMoved E t₁ ⊔ autMoved E t₂) : a = 1 := by
  have hker : autMoved E t₁ ⊔ autMoved E t₂ ≤ (normMap hcomm t₁ t₂).ker :=
    sup_le (fun x hx => MonoidHom.mem_ker.2 (normMap_moved_left hcomm h11 hx))
      (fun x hx => MonoidHom.mem_ker.2 (normMap_moved_right hcomm h11 h22 h3 hx))
  have h6 : a ^ 6 = 1 := by
    have := MonoidHom.mem_ker.1 (hker ha)
    rwa [normMap_fixed hcomm h1 h2] at this
  have hcop : Nat.Coprime 6 p := by
    refine (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_))
    have hle : p ≤ 6 := Nat.le_of_dvd (by norm_num) hd
    interval_cases p
    · norm_num at hd
    · exact absurd hp (by norm_num)
  have := pow_gcd_eq_one.2 ⟨h6, hpow a⟩
  rwa [hcop, pow_one] at this

end Norm

theorem inf_eq_bot_of_card_prime {X : Type*} [Group X] [Finite X] {A B : Subgroup X} {q : ℕ}
    (hq : q.Prime) (hA : Nat.card A = q) (hB : Nat.card B = q) (hne : A ≠ B) : A ⊓ B = ⊥ := by
  have hd : Nat.card ↥(A ⊓ B) ∣ q := hA ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hq).1 hd with h1 | h1
  · exact Subgroup.card_eq_one.1 h1
  · exfalso
    apply hne
    have e1 : A ⊓ B = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hA])
    have e2 : A ⊓ B = B := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, hB])
    exact e1.symm.trans e2

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem gp_conj_pair : ∀ g₁ γ : Sec1322Fin.Gp, g₁ * g₁ = 1 →
    g₁ * (γ * g₁ * γ⁻¹) ≠ (γ * g₁ * γ⁻¹) * g₁ → (g₁ * (γ * g₁ * γ⁻¹)) ^ 3 = 1 := by
  decide +kernel

section Geometry

variable [Finite G]

omit [Finite G] in
theorem orderOf_eq_of_ne_one (hd : RefFacts.ElemData p E) {x : E} (hx : x ≠ 1) :
    orderOf x = p := by
  have : Fact p.Prime := ⟨hd.prime⟩
  exact orderOf_eq_prime (hd.pow x) hx

theorem zpowers_eq_of_card_prime (hd : RefFacts.ElemData p E) {B : Subgroup E}
    (hB : Nat.card B = p) {x : E} (hxB : x ∈ B) (hx : x ≠ 1) : Subgroup.zpowers x = B :=
  Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxB)
    (by rw [hB, Nat.card_zpowers, orderOf_eq_of_ne_one hd hx])

omit [Finite G] in
theorem exists_ne_one_of_card_prime (hd : RefFacts.ElemData p E) {B : Subgroup E}
    (hB : Nat.card B = p) : ∃ x ∈ B, x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : B = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
  rw [this, Subgroup.card_bot] at hB
  exact hd.prime.one_lt.ne hB

theorem pair_geometry (hd : RefFacts.ElemData p E) (hcard : Nat.card E = p ^ 3)
    {t₁ t₂ : MulAut E} (h₁ : IsAutReflection p E t₁) {v : E} (hv1 : v ≠ 1) (hv₁ : t₁ v = v)
    (hcardP : Nat.card ↥(autMoved E t₁ ⊔ autMoved E t₂) = p ^ 2)
    (hvP : v ∉ autMoved E t₁ ⊔ autMoved E t₂) :
    ∃ c₀ x : E, c₀ ≠ 1 ∧ c₀ ∈ autMoved E t₁ ⊔ autMoved E t₂ ∧ t₁ c₀ = c₀ ∧
      x ∈ autMoved E t₁ ∧ x ≠ 1 ∧
      autMoved E t₁ ⊔ autMoved E t₂ = Subgroup.zpowers c₀ ⊔ Subgroup.zpowers x ∧
      autFixed E t₁ = Subgroup.zpowers v ⊔ Subgroup.zpowers c₀ ∧
      Subgroup.zpowers v ⊔ (autMoved E t₁ ⊔ autMoved E t₂) = ⊤ := by
  have hp := hd.prime
  set P : Subgroup E := autMoved E t₁ ⊔ autMoved E t₂ with hPdef
  have hL₁P : autMoved E t₁ ≤ P := le_sup_left
  have hcardC : Nat.card ↥(P ⊓ autFixed E t₁) = p := by
    have h := RefFacts.card_eq_inf_fixed_mul hd h₁ hL₁P
    rw [hcardP, pow_two] at h
    exact (Nat.eq_of_mul_eq_mul_right hp.pos h).symm
  obtain ⟨c₀, hc₀, hc₀1⟩ := exists_ne_one_of_card_prime hd hcardC
  obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_card_prime hd h₁.2
  have hzc : Subgroup.zpowers c₀ = P ⊓ autFixed E t₁ := zpowers_eq_of_card_prime hd hcardC hc₀ hc₀1
  have hzx : Subgroup.zpowers x = autMoved E t₁ := zpowers_eq_of_card_prime hd h₁.2 hx hx1
  have hPgen : P = Subgroup.zpowers c₀ ⊔ Subgroup.zpowers x := by
    rw [hzc, hzx]
    exact (RefFacts.inf_fixed_sup_autMoved hd h₁ hL₁P).symm
  have hc₀fix : t₁ c₀ = c₀ := hc₀.2
  have hvord : orderOf v = p := orderOf_eq_of_ne_one hd hv1
  have hzv : Nat.card ↥(Subgroup.zpowers v) = p := by rw [Nat.card_zpowers, hvord]
  have hzc' : Nat.card ↥(Subgroup.zpowers c₀) = p := by
    rw [Nat.card_zpowers, orderOf_eq_of_ne_one hd hc₀1]
  have hvz : Subgroup.zpowers v ⊓ P = ⊥ := by
    have hd' : Nat.card ↥(Subgroup.zpowers v ⊓ P) ∣ p := hzv ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hp).1 hd' with h1 | h1
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      apply hvP
      have e : Subgroup.zpowers v ⊓ P = Subgroup.zpowers v :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hzv])
      have : v ∈ Subgroup.zpowers v ⊓ P := by rw [e]; exact Subgroup.mem_zpowers v
      exact this.2
  refine ⟨c₀, x, hc₀1, hc₀.1, hc₀fix, hx, hx1, hPgen, ?_, ?_⟩
  ·
    have hle : Subgroup.zpowers v ⊔ Subgroup.zpowers c₀ ≤ autFixed E t₁ :=
      sup_le (Subgroup.zpowers_le.2 hv₁) (Subgroup.zpowers_le.2 hc₀fix)
    have hdisj : Subgroup.zpowers v ⊓ Subgroup.zpowers c₀ = ⊥ := by
      rw [eq_bot_iff, ← hvz]
      exact inf_le_inf_left _ (Subgroup.zpowers_le.2 hc₀.1)
    have hcardsup : Nat.card ↥(Subgroup.zpowers v ⊔ Subgroup.zpowers c₀) = p ^ 2 := by
      rw [Torsion37.card_sup_of_commute_disjoint (fun k _ l _ => hd.comm k l)
        (disjoint_iff.2 hdisj), hzv, hzc', pow_two]
    symm
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardsup, card_autFixed hd hcard h₁])
  ·
    rw [← Subgroup.card_eq_iff_eq_top, Torsion37.card_sup_of_commute_disjoint
      (fun k _ l _ => hd.comm k l) (disjoint_iff.2 hvz), hzv, hcardP, hcard]
    ring

end Geometry

section Hyp

variable [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {f r : ℕ} {R : Subgroup G}
  {s s' zs : MulAut E}

theorem exists_pair (hGA : CFSG.Open.GriessAllModelsStatement)
    (H : Hyp G p A c L E f r R s s' zs) :
    ∃ (t : MulAut E) (v : E), t ∈ clsOf p E s ∧ s * t ≠ t * s ∧ (s * t) ^ 3 = 1 ∧ v ≠ 1 ∧
      s v = v ∧ t v = v ∧ Nat.card ↥(autMoved E s ⊔ autMoved E t) = p ^ 2 ∧
      v ∉ autMoved E s ⊔ autMoved E t := by
  have h := H.h12
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hcard : Nat.card E = p ^ 3 := by rw [H.hEA]; exact h.A_card
  have hd := RefFacts.ElemData.of_isElementaryAbelian hp hp2 h.E_elem
  obtain ⟨eX⟩ := H.hweyl
  obtain ⟨Bd⟩ := exists_bridge h H.hF13 hcard eX
  obtain ⟨a, a', b, g₀, ha, ha', hb, haL, ha'L, hbL, hss, hcomm, hne, hab4, ⟨h₁, hh₁X, hh₁⟩,
    hucen, hfixu, hfixc, hg₀X, hg₀, hza, hzb, hzab, hzba⟩ := refData hGA H
  have haS : a = s ∨ a = s' := by
    rcases hss with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact Or.inl h1.symm
    · exact Or.inr h1.symm
  have ha'cls : a' ∈ clsOf p E a := ⟨h₁, hh₁X, hh₁⟩
  have hscls : s ∈ clsOf p E a := by
    rcases hss with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]; exact mem_clsOf_self p E a
    · rw [h1]; exact ha'cls
  have hacls : a ∈ clsOf p E s := by
    rcases hss with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [← h1]; exact mem_clsOf_self p E s
    · refine ⟨h₁⁻¹, Subgroup.inv_mem _ hh₁X, ?_⟩
      rw [h1, ← hh₁]
      group
  have hcls' : ∀ t ∈ clsOf p E a, t ∈ clsOf p E s := fun t ht => clsOf_trans hacls ht
  obtain ⟨u, hu, hau⟩ : ∃ u ∈ clsOf p E a, a * u ≠ u * a := by
    rcases bridge_conn Bd h hcard ha hb H.hzs hab4 (H.hzc a haL) (H.hzc b hbL) hza hzb hzab hzba
        ⟨g₀, hg₀X, hg₀⟩ ha'cls with h1 | h1 | ⟨u, hu, hau, -⟩
    · exact absurd h1.symm hne
    · exact absurd hcomm h1
    · exact ⟨u, hu, hau⟩
  have hrefl : ∀ t ∈ clsOf p E a, IsAutReflection p E t ∧ t ∈ reflectionGroup p E := by
    intro t ht
    obtain ⟨hts, -, -, -⟩ := class_facts H haS ht
    exact ⟨hts.1, Subgroup.subset_closure hts⟩
  have hacl : a ∈ clsOf p E a := mem_clsOf_self p E a
  have ht₁ := (hrefl a hacl).1
  have ht₂ := (hrefl u hu).1
  have hpow3 : (a * u) ^ 3 = 1 := by
    obtain ⟨g₁, rfl, hg₁2, -, -⟩ := Bd.refl_data h hcard ((class_facts H haS hacl).1)
    obtain ⟨γ, hγX, rfl⟩ := hu
    obtain ⟨γ', rfl⟩ := Bd.surj γ hγX
    have hinv : ∀ g : Sec1322Fin.Gp, Bd.φ g⁻¹ = (Bd.φ g)⁻¹ := fun g => map_inv Bd.φ g
    have hnc : g₁ * (γ' * g₁ * γ'⁻¹) ≠ (γ' * g₁ * γ'⁻¹) * g₁ := fun h1 => hau (by
      have := congrArg Bd.φ h1
      simp only [map_mul, hinv] at this
      exact this)
    have := gp_conj_pair g₁ γ' hg₁2 hnc
    have h2 := congrArg Bd.φ this
    simp only [map_pow, map_mul, hinv, map_one] at h2
    exact h2
  obtain ⟨g, hgX, hg⟩ := id hscls
  have hu' : g * u * g⁻¹ ∈ clsOf p E a := clsOf_trans hu ⟨g, hgX, rfl⟩
  set u' : MulAut E := g * u * g⁻¹ with hu'def
  have hsr : IsAutReflection p E s := (hrefl s hscls).1
  have hu'r : IsAutReflection p E u' := (hrefl u' hu').1
  have hss' : s * u' = g * (a * u) * g⁻¹ := by rw [hu'def, ← hg]; group
  have hu's : u' * s = g * (u * a) * g⁻¹ := by rw [hu'def, ← hg]; group
  have hnc : s * u' ≠ u' * s := by
    intro h1
    apply hau
    rw [hss', hu's] at h1
    exact mul_left_cancel (mul_right_cancel h1)
  have hpow3' : (s * u') ^ 3 = 1 := by
    rw [hss', conj_pow, hpow3, mul_one, mul_inv_cancel]
  have h11 : s * s = 1 := RefFacts.mul_self_eq_one hsr
  have h22 : u' * u' = 1 := RefFacts.mul_self_eq_one hu'r
  obtain ⟨v, hv1, hv₁, hv₂⟩ := exists_fixed_pair hd hcard hsr hu'r
  have hpm : ∀ x : E, x ^ p = 1 := hd.pow
  have hl : autMoved E s ≠ autMoved E u' := by
    intro heq
    have h1 := mul_pow_eq_one_of_same_moved hd hsr hu'r heq
    have hcop : Nat.Coprime 3 p := by
      refine (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hdv => ?_))
      have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hdv
      omega
    have h2 : (s * u') = 1 := by
      have := pow_gcd_eq_one.2 ⟨hpow3', h1⟩
      rwa [hcop, pow_one] at this
    apply hnc
    have h3 : u' = s⁻¹ := eq_inv_of_mul_eq_one_right h2
    have h4 : s⁻¹ = s := inv_eq_of_mul_eq_one_right h11
    rw [h3, h4]
  have hdisj : autMoved E s ⊓ autMoved E u' = ⊥ :=
    inf_eq_bot_of_card_prime hp hsr.2 hu'r.2 hl
  have hcardP : Nat.card ↥(autMoved E s ⊔ autMoved E u') = p ^ 2 := by
    rw [Torsion37.card_sup_of_commute_disjoint (fun k _ l _ => hd.comm k l)
      (disjoint_iff.2 hdisj), hsr.2, hu'r.2, pow_two]
  have hvP : v ∉ autMoved E s ⊔ autMoved E u' := fun hv => hv1
    (fixed_inf_lines hd.comm h11 h22 hpow3' hp hp5 hpm hv₁ hv₂ hv)
  exact ⟨u', v, hcls' u' hu', hnc, hpow3', hv1, hv₁, hv₂, hcardP, hvP⟩

end Hyp

end CFSG.RankThree.PartOne.Q1327T
