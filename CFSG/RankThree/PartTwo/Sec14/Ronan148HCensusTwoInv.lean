module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HCensusGen

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
open scoped Pointwise

@[expose] def TwoInvCent (S : Type) [Group S] : Prop :=
  ∀ T : Sylow 3 S, ∃ x₁ ∈ (T : Subgroup S), ∃ x₂ ∈ (T : Subgroup S), ∃ R₁ R₂ : Subgroup S,
    (∀ g, g ∈ R₁ ↔ g * x₁ = x₁ * g ∧ g ^ 2 = 1) ∧ (∀ g, g ∈ R₂ ↔ g * x₂ = x₂ * g ∧ g ^ 2 = 1) ∧
    Nat.card R₁ = 4 ∧ Nat.card R₂ = 4 ∧ R₁ ≠ R₂

theorem TwoInvCent.of_mulEquiv {S T : Type} [Group S] [Group T] [Finite T] (e : T ≃* S)
    (h : TwoInvCent S) : TwoInvCent T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro U
  obtain ⟨x₁, hx₁, x₂, hx₂, R₁, R₂, h₁, h₂, hc₁, hc₂, hne⟩ :=
    h (U.mapSurjective (f := e.toMonoidHom) e.surjective)
  change x₁ ∈ (U : Subgroup T).map e.toMonoidHom at hx₁
  change x₂ ∈ (U : Subgroup T).map e.toMonoidHom at hx₂
  obtain ⟨y₁, hy₁, rfl⟩ := hx₁
  obtain ⟨y₂, hy₂, rfl⟩ := hx₂
  have hiff : ∀ (y : T) (R : Subgroup S),
      (∀ g, g ∈ R ↔ g * e.toMonoidHom y = e.toMonoidHom y * g ∧ g ^ 2 = 1) →
      ∀ g, g ∈ R.comap e.toMonoidHom ↔ g * y = y * g ∧ g ^ 2 = 1 := by
    intro y R hR g
    rw [Subgroup.mem_comap, hR]
    simp only [MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨e.injective (by rw [map_mul, map_mul]; exact h1),
        e.injective (by rw [map_pow, map_one]; exact h2)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [← map_mul, ← map_mul, h1], by rw [← map_pow, h2, map_one]⟩
  have hcard : ∀ R : Subgroup S, Nat.card (R.comap e.toMonoidHom) = Nat.card R := fun R =>
    Nat.card_congr (e.toEquiv.subtypeEquiv fun g => Iff.rfl)
  refine ⟨y₁, hy₁, y₂, hy₂, R₁.comap e.toMonoidHom, R₂.comap e.toMonoidHom, hiff y₁ R₁ h₁,
    hiff y₂ R₂ h₂, by rw [hcard, hc₁], by rw [hcard, hc₂], fun h12 => hne ?_⟩
  exact Subgroup.comap_injective e.surjective h12

section Row

set_option linter.unusedSectionVars false


variable {X : Type} [Group X] [Finite X] {P L Q : Subgroup X}

theorem OLCfg.false_of_twoInvCent (hcfg : OLCfg P L Q) (h : TwoInvCent ↥L) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : ↥P →* MulAut ↥L :=
    { toFun := fun p => conjAut (hcfg.normL p.2)
      map_one' := (conjAut_eq_one_iff _).mpr fun l _ => by simp
      map_mul' := fun p q => conjAut_mul (hcfg.normL p.2) (hcfg.normL q.2) }
  letI : MulDistribMulAction ↥P ↥L := MulDistribMulAction.compHom ↥L φ
  have hPp : IsPGroup 3 P := fun x => ⟨1, Subtype.ext (by simpa using hcfg.e27.1.2 x x.2)⟩
  obtain ⟨T, hT⟩ : ∃ T : Sylow 3 ↥L, ∀ p : ↥P, p • T = T := by
    have h1 := hPp.card_modEq_card_fixedPoints (Sylow 3 ↥L)
    have h2 := card_sylow_modEq_one 3 ↥L
    have h3 : Nat.card (MulAction.fixedPoints ↥P (Sylow 3 ↥L)) ≠ 0 := by
      intro h0
      rw [h0] at h1
      have h4 := h2.symm.trans h1
      exact absurd h4 (by decide)
    obtain ⟨⟨T, hT⟩⟩ := (Nat.card_ne_zero.mp h3).1
    exact ⟨T, hT⟩
  set TX : Subgroup X := (T : Subgroup L).map L.subtype with hTXdef
  have hTX : ∀ p ∈ P, ∀ t ∈ TX, p * t * p⁻¹ ∈ TX := by
    intro p hp t ht
    obtain ⟨t', ht', rfl⟩ := ht
    have h1 : (⟨p, hp⟩ : ↥P) • (T : Subgroup L) = T :=
      congrArg (fun U : Sylow 3 ↥L => (U : Subgroup L)) (hT ⟨p, hp⟩)
    have h2 : (⟨p, hp⟩ : ↥P) • t' ∈ (T : Subgroup L) := by
      rw [← h1]
      exact Subgroup.smul_mem_pointwise_smul t' _ _ ht'
    exact ⟨_, h2, coe_conjAut_apply (hcfg.normL hp) t'⟩
  have hTXp : IsPGroup 3 TX := T.isPGroup'.map L.subtype
  have hPTX : P ≤ Subgroup.normalizer (TX : Set X) := le_normalizer_of_conj_mem' hTX
  have hsup : IsPGroup 3 (TX ⊔ P : Subgroup X) := IsPGroup.to_sup_of_normal_left' hTXp hPp hPTX
  obtain ⟨-, hcomm⟩ := commutator_mem_center_of_isPGroup hcfg.triple hsup
  obtain ⟨x₁, hx₁, x₂, hx₂, R₁, R₂, h₁, h₂, hc₁, hc₂, hne⟩ := h T
  have key : ∀ x : L, x ∈ (T : Subgroup L) → ∀ R : Subgroup L,
      (∀ g, g ∈ R ↔ g * x = x * g ∧ g ^ 2 = 1) → Nat.card R = 4 → R.map L.subtype = Q := by
    intro x hx R hR hc
    have hR3 : ¬ 3 ∣ Nat.card (R.map L.subtype) := by
      rw [Subgroup.card_map_of_injective L.subtype_injective, hc]
      norm_num
    have hxTX : (x : X) ∈ TX ⊔ P := le_sup_left (a := TX) ⟨x, hx, rfl⟩
    have hPR : P ≤ Subgroup.normalizer ((R.map L.subtype : Subgroup X) : Set X) := by
      refine le_normalizer_of_conj_mem' fun p hp r hr => ?_
      obtain ⟨g, hg, rfl⟩ := hr
      have hpL := hcfg.normL hp
      have hg'v : ((conjAut hpL g : L) : X) = p * g * p⁻¹ := coe_conjAut_apply hpL g
      obtain ⟨hgx, hg2⟩ := (hR g).mp hg
      have hgx' : (g : X) * x = x * g := congrArg Subtype.val hgx
      have hg2' : (g : X) ^ 2 = 1 := congrArg Subtype.val hg2
      obtain ⟨c, hcdef⟩ : ∃ c : X, c = (x : X) * p * (x : X)⁻¹ * p⁻¹ := ⟨_, rfl⟩
      have hcZ : c ∈ Subgroup.center X := hcdef ▸ hcomm _ hxTX p (le_sup_right (b := P) hp)
      have hcz : ∀ y : X, y * c = c * y := Subgroup.mem_center_iff.mp hcZ
      have hcx : (x : X) = c * (p * x * p⁻¹) := by rw [hcdef]; group
      refine ⟨conjAut hpL g, (hR _).mpr ⟨Subtype.ext ?_, Subtype.ext ?_⟩, hg'v⟩
      · rw [Subgroup.coe_mul, Subgroup.coe_mul, hg'v]
        calc p * g * p⁻¹ * x = p * g * p⁻¹ * (c * (p * x * p⁻¹)) := by rw [← hcx]
          _ = p * g * p⁻¹ * c * (p * x * p⁻¹) := by group
          _ = c * (p * g * p⁻¹) * (p * x * p⁻¹) := by rw [hcz (p * g * p⁻¹)]
          _ = c * (p * ((g : X) * x) * p⁻¹) := by group
          _ = c * (p * ((x : X) * g) * p⁻¹) := by rw [hgx']
          _ = c * (p * x * p⁻¹) * (p * g * p⁻¹) := by group
          _ = x * (p * g * p⁻¹) := by rw [← hcx]
      · rw [SubgroupClass.coe_pow, hg'v, conj_pow, hg2']
        simp
    have hRQ : R.map L.subtype ≤ Q := hcfg.inv _ ((Subgroup.map_subtype_le R).trans le_sup_left)
      ⟨le_top, isPiSubgroup_of_not_dvd hR3, hPR⟩
    exact Subgroup.eq_of_le_of_card_ge hRQ (by
      rw [hcfg.klein.card_four, Subgroup.card_map_of_injective L.subtype_injective, hc])
  exact hne (Subgroup.map_injective L.subtype_injective
    ((key x₁ hx₁ R₁ h₁ hc₁).trans (key x₂ hx₂ R₂ h₂ hc₂).symm))

theorem olRow_of_twoInvCent (S : Type) [Group S] (h : TwoInvCent S) :
    OLRow (fun T _ => Nonempty (T ≃* S)) := by
  intro X _ _ P L Q hcfg ⟨e⟩
  exact hcfg.false_of_twoInvCent (h.of_mulEquiv e)

end Row

section Lift

variable {G : Type} [Group G] [Finite G] {Z : Subgroup G} [Z.Normal]

theorem commute_of_mk_commute (hZ : Z ≤ Subgroup.center G) (h3 : Nat.card Z = 3) {g x : G}
    (hg : g ^ 2 = 1)
    (hgx : (g : G ⧸ Z) * (x : G ⧸ Z) = (x : G ⧸ Z) * (g : G ⧸ Z)) : g * x = x * g := by
  have hc : g * x * g⁻¹ * x⁻¹ ∈ Z := by
    have : ((g * x * g⁻¹ * x⁻¹ : G) : G ⧸ Z) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, hgx]
      group
    exact (QuotientGroup.eq_one_iff _).mp this
  obtain ⟨c, hcdef⟩ : ∃ c : G, c = g * x * g⁻¹ * x⁻¹ := ⟨_, rfl⟩
  have hcZ : c ∈ Z := hcdef ▸ hc
  have hcz : ∀ y : G, y * c = c * y := Subgroup.mem_center_iff.mp (hZ hcZ)
  have h1 : g * x * g⁻¹ = c * x := by rw [hcdef]; group
  have hgg : g * g = 1 := by rw [← pow_two, hg]
  have h2 : x = c * (c * x) := by
    calc x = (g * g) * x * (g * g)⁻¹ := by rw [hgg]; group
      _ = g * (g * x * g⁻¹) * g⁻¹ := by group
      _ = g * (c * x) * g⁻¹ := by rw [h1]
      _ = (g * c) * x * g⁻¹ := by group
      _ = (c * g) * x * g⁻¹ := by rw [hcz g]
      _ = c * (g * x * g⁻¹) := by group
      _ = c * (c * x) := by rw [h1]
  have hc2 : c * c = 1 := by
    have := h2
    calc c * c = c * (c * x) * x⁻¹ := by group
      _ = x * x⁻¹ := by rw [← this]
      _ = 1 := mul_inv_cancel x
  have hc3 : c ^ 3 = 1 := by
    have := pow_card_eq_one' (G := Z) (x := ⟨c, hcZ⟩)
    rw [h3] at this
    exact congrArg Subtype.val this
  have hc1 : c = 1 := by
    calc c = c ^ 3 * (c * c)⁻¹ := by rw [pow_succ, pow_two]; group
      _ = 1 := by rw [hc3, hc2]; group
  calc g * x = g * x * g⁻¹ * g := by group
    _ = c * x * g := by rw [h1]
    _ = x * g := by rw [hc1, one_mul]

theorem exists_invSub_lift (hZ : Z ≤ Subgroup.center G) (h3 : Nat.card Z = 3) (x : G)
    (R : Subgroup (G ⧸ Z))
    (hR : ∀ g, g ∈ R ↔ g * (x : G ⧸ Z) = (x : G ⧸ Z) * g ∧ g ^ 2 = 1) (hc : Nat.card R = 4) :
    ∃ R' : Subgroup G, (∀ g, g ∈ R' ↔ g * x = x * g ∧ g ^ 2 = 1) ∧ Nat.card R' = 4 ∧
      R'.map (QuotientGroup.mk' Z) = R := by
  have hz3 : ∀ z ∈ Z, z ^ 3 = 1 := fun z hz => by
    have := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
    rw [h3] at this
    exact congrArg Subtype.val this
  have hRmk : ∀ g : G, g * x = x * g → g ^ 2 = 1 → (g : G ⧸ Z) ∈ R := fun g h1 h2 =>
    (hR _).mpr ⟨by rw [← QuotientGroup.mk_mul, h1, QuotientGroup.mk_mul],
      by rw [← QuotientGroup.mk_pow, h2, QuotientGroup.mk_one]⟩
  have hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
    intro a ha b hb
    have ha2 := ((hR a).mp ha).2
    have hb2 := ((hR b).mp hb).2
    have hab2 := ((hR (a * b)).mp (Subgroup.mul_mem _ ha hb)).2
    have hai : a⁻¹ = a := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ha2]
    have hbi : b⁻¹ = b := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hb2]
    have habi : (a * b)⁻¹ = a * b := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hab2]
    calc a * b = (a * b)⁻¹ := habi.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hai, hbi]
  let R' : Subgroup G :=
    { carrier := {g | g * x = x * g ∧ g ^ 2 = 1}
      one_mem' := ⟨by group, by group⟩
      mul_mem' := by
        rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
        have hgh : g * h = h * g := by
          have h1 := hRcomm _ (hRmk g hg1 hg2) _ (hRmk h hh1 hh2)
          have hmk : ((g * h : G) : G ⧸ Z) * (h : G ⧸ Z)⁻¹ = (g : G ⧸ Z) := by
            rw [QuotientGroup.mk_mul]; group
          have h2 : ((g : G) : G ⧸ Z) * (h : G ⧸ Z) = (h : G ⧸ Z) * (g : G ⧸ Z) := h1
          exact commute_of_mk_commute hZ h3 hg2 h2
        refine ⟨?_, ?_⟩
        · calc g * h * x = g * (h * x) := by group
            _ = g * (x * h) := by rw [hh1]
            _ = (g * x) * h := by group
            _ = (x * g) * h := by rw [hg1]
            _ = x * (g * h) := by group
        · calc (g * h) ^ 2 = g * h * (g * h) := pow_two _
            _ = g * (h * g) * h := by group
            _ = g * (g * h) * h := by rw [hgh]
            _ = g ^ 2 * h ^ 2 := by rw [pow_two, pow_two]; group
            _ = 1 := by rw [hg2, hh2, one_mul]
      inv_mem' := by
        rintro g ⟨hg1, hg2⟩
        have hgi : g⁻¹ = g := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hg2]
        rw [Set.mem_setOf_eq, hgi]
        exact ⟨hg1, hg2⟩ }
  have hmem : ∀ g, g ∈ R' ↔ g * x = x * g ∧ g ^ 2 = 1 := fun g => Iff.rfl
  let f : ↥R' → ↥R := fun g => ⟨(g : G), hRmk g ((hmem g).mp g.2).1 ((hmem g).mp g.2).2⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    have hab' : ((a : G) : G ⧸ Z) = ((b : G) : G ⧸ Z) := congrArg Subtype.val hab
    rw [QuotientGroup.eq] at hab'
    obtain ⟨z, hzdef⟩ : ∃ z : G, z = (a : G)⁻¹ * b := ⟨_, rfl⟩
    have hzZ : z ∈ Z := hzdef ▸ hab'
    have hcz : ∀ y : G, y * z = z * y := Subgroup.mem_center_iff.mp (hZ hzZ)
    have hb : (b : G) = a * z := by rw [hzdef]; group
    have ha2 := ((hmem a).mp a.2).2
    have hb2 := ((hmem b).mp b.2).2
    have hz2 : z ^ 2 = 1 := by
      have e1 : (b : G) ^ 2 = (a : G) ^ 2 * z ^ 2 := by
        rw [hb, pow_two, pow_two, pow_two]
        calc (a : G) * z * (a * z) = a * (z * a) * z := by group
          _ = a * (a * z) * z := by rw [← hcz a]
          _ = a * a * (z * z) := by group
      rw [hb2, ha2, one_mul] at e1
      exact e1.symm
    have hz1 : z = 1 := by
      calc z = z ^ 3 * (z ^ 2)⁻¹ := by rw [pow_succ, pow_two]; group
        _ = 1 := by rw [hz3 z hzZ, hz2]; group
    apply Subtype.ext
    rw [hb, hz1, mul_one]
  have hfsurj : Function.Surjective f := by
    rintro ⟨r, hr⟩
    obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective r
    have hr2 := ((hR _).mp hr).2
    have hg₀2 : g₀ ^ 2 ∈ Z := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hr2]
    have hg2 : (g₀ ^ 3) ^ 2 = 1 := by
      calc (g₀ ^ 3) ^ 2 = (g₀ ^ 2) ^ 3 := by rw [← pow_mul, ← pow_mul]
        _ = 1 := hz3 _ hg₀2
    have hgr : ((g₀ ^ 3 : G) : G ⧸ Z) = (g₀ : G ⧸ Z) := by
      rw [QuotientGroup.mk_pow]
      calc (g₀ : G ⧸ Z) ^ 3 = (g₀ : G ⧸ Z) ^ 2 * g₀ := pow_succ _ 2
        _ = g₀ := by rw [hr2, one_mul]
    have hgx : g₀ ^ 3 * x = x * g₀ ^ 3 := by
      apply commute_of_mk_commute hZ h3 hg2
      rw [hgr]
      exact ((hR _).mp hr).1
    exact ⟨⟨g₀ ^ 3, hgx, hg2⟩, Subtype.ext hgr⟩
  refine ⟨R', hmem, ?_, ?_⟩
  · rw [← hc]
    exact Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
  · apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      exact (f ⟨g, hg⟩).2
    · intro r hr
      obtain ⟨g, hg⟩ := hfsurj ⟨r, hr⟩
      exact ⟨g, g.2, congrArg Subtype.val hg⟩

theorem twoInvCent_of_quotient (hZ : Z ≤ Subgroup.center G) (h3 : Nat.card Z = 3)
    (h : TwoInvCent (G ⧸ Z)) : TwoInvCent G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro T
  obtain ⟨y₁, hy₁, y₂, hy₂, R₁, R₂, h₁, h₂, hc₁, hc₂, hne⟩ :=
    h (T.mapSurjective (f := QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z))
  change y₁ ∈ (T : Subgroup G).map (QuotientGroup.mk' Z) at hy₁
  change y₂ ∈ (T : Subgroup G).map (QuotientGroup.mk' Z) at hy₂
  obtain ⟨x₁, hx₁, rfl⟩ := hy₁
  obtain ⟨x₂, hx₂, rfl⟩ := hy₂
  obtain ⟨S₁, hS₁, hd₁, hm₁⟩ := exists_invSub_lift hZ h3 x₁ R₁ h₁ hc₁
  obtain ⟨S₂, hS₂, hd₂, hm₂⟩ := exists_invSub_lift hZ h3 x₂ R₂ h₂ hc₂
  refine ⟨x₁, hx₁, x₂, hx₂, S₁, S₂, hS₁, hS₂, hd₁, hd₂, fun h12 => hne ?_⟩
  rw [← hm₁, ← hm₂, h12]

end Lift

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
