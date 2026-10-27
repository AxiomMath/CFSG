module

public import CFSG.Quasithin.EmptyFaithful.S152He9H
public import CFSG.Quasithin.EmptyFaithful.S152L08A

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

namespace WrH

variable {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5}

theorem mem_M_of_mem_Sw (hs : Setting152 T Mc M) (hH : IsHStar T M H)
    (h1519 : Lemma1519Concl T Mc M) (h : WrH H T K₁ K₂ π) {x : G} (hx : x ∈ H)
    (hπ : π ⟨x, hx⟩ ∈ W5.Sw) : x ∈ M := by
  have hmp := S152L08.minParabolic_of_hStar hs hH h1519.seven_normalizer
  set X : Subgroup G := (W5.Sw.comap π).map H.subtype with hX
  have hTX : T ≤ X := by
    intro t ht
    have htH : t ∈ H := hH.1.1 ht
    refine ⟨⟨t, htH⟩, ?_, rfl⟩
    exact h.T_le ⟨⟨t, htH⟩, ht, rfl⟩
  have hXH : X < H := by
    refine lt_of_le_of_ne (Subgroup.map_subtype_le _) ?_
    intro heq
    apply W5.Sw_ne_top
    rw [eq_top_iff]
    intro w _
    obtain ⟨y, rfl⟩ := h.data.surj w
    have : (y : G) ∈ X := by rw [heq]; exact y.2
    obtain ⟨y', hy', hyy⟩ := this
    have : y' = y := Subtype.ext hyy
    rw [← this]
    exact hy'
  have := hmp.le_of_lt hTX hXH
  exact (this ⟨⟨x, hx⟩, hπ, rfl⟩).2

theorem eq_one_of_pow_two_three {X : Type*} [Group X] {x : X} {a b : ℕ} (h2 : x ^ 2 ^ a = 1)
    (h3 : x ^ 3 ^ b = 1) : x = 1 := by
  have hd : orderOf x ∣ Nat.gcd (2 ^ a) (3 ^ b) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  have hg : Nat.gcd (2 ^ a) (3 ^ b) = 1 :=
    Nat.Coprime.pow a b (by norm_num : Nat.Coprime 2 3)
  rw [hg] at hd
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)

theorem exists_E (h : WrH H T K₁ K₂ π) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      (∀ (x : G) (hx : x ∈ H), x ∈ E → π ⟨x, hx⟩ ∈ W5.E0) ∧
      ∃ (e : G) (he : e ∈ H), e ∈ E ∧ π ⟨e, he⟩ = W5.incl1 W5.c3 := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Subgroup ↥H := W5.E0.comap π
  obtain ⟨Q⟩ : Nonempty (Sylow 3 ↥P) := inferInstance
  let E' : Subgroup ↥H := (Q : Subgroup ↥P).map P.subtype
  have hE'P : ∀ x ∈ E', π x ∈ W5.E0 := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hE'p : IsPGroup 3 E' := Q.isPGroup'.map P.subtype
  have hinj : ∀ x ∈ E', π x = 1 → x = 1 := by
    intro x hx hπx
    obtain ⟨a, ha⟩ := hE'p ⟨x, hx⟩
    have hxk : x ∈ CFSG.Open.pCore 2 ↥H := by rw [← h.ker_eq]; exact hπx
    obtain ⟨b, hb⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 :
      IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥H)) ⟨x, hxk⟩
    exact eq_one_of_pow_two_three (a := b) (b := a)
      (by simpa using congrArg (fun y : ↥(CFSG.Open.pCore 2 ↥H) => (y : ↥H)) hb)
      (by simpa using congrArg (fun y : ↥E' => (y : ↥H)) ha)
  let ψ : ↥E' →* ↥W5.E0 := (π.comp E'.subtype).codRestrict W5.E0 (fun x => hE'P x.1 x.2)
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have h1 : π (x : ↥H) = π (y : ↥H) := congrArg Subtype.val hxy
    have h2 : π ((x : ↥H)⁻¹ * y) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
    have := hinj _ (E'.mul_mem (E'.inv_mem x.2) y.2) h2
    exact Subtype.ext (inv_mul_eq_one.1 this)
  have hle : Nat.card ↥E' ≤ 9 := by
    rw [← W5.card_E0]
    exact Nat.card_le_card_of_injective _ hψinj
  have h9 : 9 ∣ Nat.card ↥E' := by
    have hP : 9 ∣ Nat.card ↥P := by
      let χ : ↥P →* W5 := π.comp P.subtype
      have hrange : χ.range = W5.E0 := by
        ext w
        constructor
        · rintro ⟨y, rfl⟩
          exact y.2
        · intro hw
          obtain ⟨y, rfl⟩ := h.data.surj w
          exact ⟨⟨y, hw⟩, rfl⟩
      have := Subgroup.card_mul_index χ.ker
      rw [Subgroup.index_ker, hrange, W5.card_E0] at this
      exact ⟨Nat.card ↥χ.ker, by rw [← this]; ring⟩
    have hcardE' : Nat.card ↥E' = Nat.card ↥(Q : Subgroup ↥P) :=
      (Nat.card_congr (Subgroup.equivMapOfInjective _ P.subtype P.subtype_injective).toEquiv).symm
    rw [hcardE']
    have hQ := (Q : Subgroup ↥P).card_mul_index
    have hcop : Nat.Coprime 9 (Q : Subgroup ↥P).index := by
      have := Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
        Q.not_dvd_index)
      simpa using this
    exact hcop.dvd_of_dvd_mul_right (hQ ▸ hP)
  have hcard : Nat.card ↥E' = 9 := by
    have hpos : 0 < Nat.card ↥E' := Nat.card_pos
    obtain ⟨k, hk⟩ := h9
    omega
  have hψbij : Function.Bijective ψ :=
    hψinj.bijective_of_nat_card_le (by rw [W5.card_E0, hcard])
  have hcomm : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
    intro x hx y hy
    have h1 := hψinj (a₁ := (⟨x, hx⟩ : ↥E') * ⟨y, hy⟩) (a₂ := (⟨y, hy⟩ : ↥E') * ⟨x, hx⟩)
      (Subtype.ext (by
        simp only [map_mul, Subgroup.coe_mul]
        exact W5.E0_comm (ψ ⟨x, hx⟩).2 (ψ ⟨y, hy⟩).2))
    exact congrArg Subtype.val h1
  have hcube : ∀ x ∈ E', x ^ 3 = 1 := by
    intro x hx
    have h1 := hψinj (a₁ := (⟨x, hx⟩ : ↥E') ^ 3) (a₂ := 1)
      (Subtype.ext (by
        simp only [map_pow, Subgroup.coe_pow, map_one, Subgroup.coe_one]
        exact W5.E0_cube (ψ ⟨x, hx⟩).2))
    exact congrArg Subtype.val h1
  have hEab : IsElemAbelian 3 (E'.map H.subtype) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx, hxa⟩ := a.2
      obtain ⟨y, hy, hyb⟩ := b.2
      apply Subtype.ext
      show (a : G) * (b : G) = (b : G) * (a : G)
      rw [← hxa, ← hyb]
      have := congrArg (fun z : ↥H => (z : G)) (hcomm x hx y hy)
      simpa using this
    · rintro _ ⟨x, hx, rfl⟩
      have := congrArg (fun z : ↥H => (z : G)) (hcube x hx)
      simpa using this
  refine ⟨E'.map H.subtype, Subgroup.map_subtype_le _, hEab, ?_, ?_, ?_⟩
  · rw [← hcard]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).toEquiv).symm
  · rintro x hx ⟨y, hy, rfl⟩
    exact hE'P y hy
  · obtain ⟨e', he'⟩ := hψbij.2 ⟨W5.incl1 W5.c3, by
      refine ⟨by simp [W5.incl1_apply], by simp [W5.incl1_apply], by simp [W5.incl1_apply]⟩⟩
    refine ⟨((e' : ↥E') : ↥H), ((e' : ↥E') : ↥H).2, ⟨(e' : ↥H), e'.2, rfl⟩, ?_⟩
    have := congrArg Subtype.val he'
    exact this

theorem exists_E_le (hs : Setting152 T Mc M) (hH : IsHStar T M H)
    (h1519 : Lemma1519Concl T Mc M) (h : WrH H T K₁ K₂ π) :
    ∃ E : Subgroup G, E ≤ oTwoUpper (H ⊓ M) ∧ E ≤ H ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      ∃ (e : G) (he : e ∈ H), e ∈ E ∧ π ⟨e, he⟩ = W5.incl1 W5.c3 := by
  obtain ⟨E, hEH, hEab, hE9, hπE, e, he, heE, hπe⟩ := exists_E h
  refine ⟨E, ?_, hEH, hEab, hE9, e, he, heE, hπe⟩
  intro x hx
  apply Subgroup.subset_closure
  refine ⟨⟨hEH hx, ?_⟩, ?_⟩
  · exact mem_M_of_mem_Sw hs hH h1519 h (hEH hx) (W5.E0_le_Sw (hπE x (hEH hx) hx))
  · have h3 : x ^ 3 = 1 := hEab.2 x hx
    exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h3)

theorem borel_le_M (hs : Setting152 T Mc M) (hH : IsHStar T M H)
    (h1519 : Lemma1519Concl T Mc M) (h : WrH H T K₁ K₂ π) (hT : IsSylowTwoOf T H) :
    borelOf K₁ (T ⊓ Subgroup.normalizer (K₁ : Set G)) ≤ M := by
  set S := T ⊓ Subgroup.normalizer (K₁ : Set G) with hS
  have hSyl := isSylow_S h hT
  have hK₁N : K₁ ≤ H ⊓ Subgroup.normalizer (K₁ : Set G) :=
    le_inf h.le₁ Subgroup.le_normalizer
  have hSylK : IsSylowTwoOf (S ⊓ K₁) K₁ :=
    A4.isSylowTwoOf_inf_normal hSyl hK₁N inf_le_right
  have hSK_H : S ⊓ K₁ ≤ H := inf_le_right.trans h.le₁
  let P₁ : Subgroup ↥H := (S ⊓ K₁).subgroupOf H
  let Q₁ : Subgroup W5 := P₁.map π
  have hP₁p : IsPGroup 2 P₁ := hSylK.2.1.to_le (le_refl _) |>.of_equiv
    (Subgroup.subgroupOfEquivOfLe hSK_H).symm
  have hQA : Q₁ ≤ W5.A1 ⊓ W5.Sw := by
    rintro _ ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [← h.map₁]
      exact ⟨y, (Subgroup.mem_inf.1 hy).2, rfl⟩
    · have hy' : (y : G) ∈ S ⊓ K₁ := hy
      have hyT : (y : G) ∈ T := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hy').1).1
      exact h.T_le ⟨y, hyT, rfl⟩
  have hQne : Q₁ ≠ ⊥ := by
    intro hQ
    have hle : ((S ⊓ K₁).subgroupOf K₁) ≤ (psi₁ h).ker := by
      intro z hz
      have hz' : (Subgroup.inclusion h.le₁ z) ∈ P₁ := hz
      have : π (Subgroup.inclusion h.le₁ z) ∈ Q₁ := ⟨_, hz', rfl⟩
      rw [hQ, Subgroup.mem_bot] at this
      rw [MonoidHom.mem_ker]
      exact Subtype.ext this
    have hdvd := Subgroup.index_dvd_of_le hle
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 (psi₁_surj h), Subgroup.card_top,
      W5.card_A1] at hdvd
    exact hSylK.2.2 ((by norm_num : 2 ∣ 60).trans hdvd)
  have hQp : IsPGroup 2 Q₁ := hP₁p.map π
  intro b hb
  obtain ⟨hbK, hbN⟩ := Subgroup.mem_inf.1 hb
  have hbH : b ∈ H := h.le₁ hbK
  have hn' : (⟨b, hbH⟩ : ↥H) ∈ Subgroup.normalizer ((P₁ : Subgroup ↥H) : Set ↥H) :=
    (mem_normalizer_subtype_iff hSK_H hbH).1 hbN
  have hn : π ⟨b, hbH⟩ ∈ Subgroup.normalizer (Q₁ : Set W5) :=
    Subgroup.le_normalizer_map π ⟨_, hn', rfl⟩
  have hA : π ⟨b, hbH⟩ ∈ W5.A1 := by
    rw [← h.map₁]
    exact ⟨_, hbK, rfl⟩
  exact mem_M_of_mem_Sw hs hH h1519 h hbH (W5.normalizer_le_Sw hQA hQne hQp hA hn)

end WrH

end CFSG.Quasithin.He9
