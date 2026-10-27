module

public import CFSG.Quasithin.Vol2.Ch12Sec4C8Fin
public import CFSG.Quasithin.Vol2.Ch12Sec4L3Hyp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

@[expose] def G2HypXFact1248 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ Lb : Subgroup (MulAut V), commV Lb = ⊤ → Nat.card (fixV Lb) = 2 →
      G2NaturalDerived Lb ⊤ (fixV Lb) 1 →
      ∀ Mb : Subgroup (MulAut V), Lb < Mb → Mb ≤ Subgroup.normalizer (Lb : Set (MulAut V)) →
      ∀ U : Subgroup V, U.index = 2 → ¬ fixV Lb ≤ U →
        (∃ X : Subgroup (MulAut V), X ≤ Lb ⊓ stabSub U ∧ Nat.card X = 3 ∧ ¬ X ≤ centSub U ∧
          ∃ t ∈ Mb ⊓ Subgroup.normalizer (X : Set (MulAut V)), t ∉ stabSub U ∧
            t ^ 2 ∈ stabSub U) ∨
        ∃ Y : Subgroup (MulAut V), Y ≤ Lb ⊓ stabSub U ∧ Nat.card Y = 27 ∧
          (∀ y ∈ Y, y ^ 3 = 1) ∧ Y ⊓ centSub U = ⊥

@[expose] def G2DerivedNoOffender1248 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ Lb : Subgroup (MulAut V), commV Lb = ⊤ → Nat.card (fixV Lb) = 2 →
      G2NaturalDerived Lb ⊤ (fixV Lb) 1 →
      ∀ B : Subgroup (MulAut V), B ≤ Lb → B ≠ ⊥ → IsElemAbelian2 B →
        ¬ Nat.card V ≤ Nat.card B * Nat.card (fixV B)

namespace L3Hyp

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_hypX (hV2 : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 2 ^ 4)
    (X : Subgroup (MulAut V)) (hs : IsSimpleGroup X) (hX : Nat.card X = 168)
    (hcomm : commV X = ⊤) (hfix : Nat.card (fixV X) = 2) (U : Subgroup V) (hU : U.index = 2)
    (hnot : ¬ fixV X ≤ U) :
    ∃ Y : Subgroup (MulAut V), Y ≤ X ⊓ stabSub U ∧ Nat.card Y = 3 ∧ ¬ Y ≤ centSub U ∧
      ∃ t ∈ X ⊓ Subgroup.normalizer (Y : Set (MulAut V)), t ∉ stabSub U ∧ t ^ 2 = 1 := by
  classical
  have := hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, Y, hYle, hY3, hYU⟩ :=
    l3HyperplaneFact1248 V hV2 hcard X hs hX hcomm hfix U hU hnot
  refine ⟨Y, hYle, hY3, hYU, ?_⟩
  have hnat := binaryNaturalSL_of_card_sixteen hV2 hcard hs hX hcomm hfix
  obtain ⟨D⟩ := hnat.toL3Coord
  have h16 : Nat.card V = 16 := by rw [hcard]; norm_num
  have hind := Vol2.Ch10.SecD.isIndecompModule_of D hcomm h16
  obtain ⟨-, -, -, hinv⟩ := B4_8_2 hV2 h16 hnat hind
  obtain ⟨z, hzX, hzU⟩ : ∃ z ∈ fixV X, z ∉ U := by
    by_contra h
    push Not at h
    exact hnot h
  have hUcard : Nat.card U = 8 := by
    have h1 := U.card_mul_index
    rw [hU, h16] at h1
    omega
  have hodd : ∀ a ∈ X, a ∈ stabSub U → a ^ 2 = 1 → a = 1 := by
    intro a haX ha ha2
    by_contra ha1
    obtain ⟨hc, hrk⟩ := hinv a haX ha1 ha2
    have hF : Nat.card (fixV (Subgroup.zpowers a)) = 4 := by
      rw [card_eq_two_pow hV2, hrk]
      norm_num
    exact not_mem_stabSub_of_invol hF hc
      (fun g hg => hzX g ((Subgroup.zpowers_le.2 haX) hg)) hzU hUcard ha
  have hYX : Y ≤ X := hYle.trans inf_le_left
  set Y' : Subgroup ↥X := Y.subgroupOf X with hY'
  have hcY' : Nat.card Y' = 3 := by
    rw [hY', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYX).toEquiv, hY3]
  have hY'p : IsPGroup 3 Y' := IsPGroup.of_card (n := 1) (by rw [hcY', pow_one])
  have hidx : Y'.index = 56 := by
    have h1 := Y'.card_mul_index
    rw [hcY', hX] at h1
    omega
  have hnd : ¬ 3 ∣ Y'.index := by rw [hidx]; norm_num
  set P : Sylow 3 ↥X := hY'p.toSylow hnd with hP
  have hPY : (P : Subgroup ↥X) = Y' := IsPGroup.toSylow_coe hY'p hnd
  have hmod := card_sylow_modEq_one 3 ↥X
  have hn := Sylow.card_eq_index_normalizer P
  have hdvd : Nat.card (Sylow 3 ↥X) ∣ 56 := by
    have := Sylow.card_dvd_index P
    rwa [hPY, hidx] at this
  have hne1 : Nat.card (Sylow 3 ↥X) ≠ 1 := by
    intro h1
    rw [h1] at hn
    have hNtop := Subgroup.index_eq_one.1 hn.symm
    have hPn : (P : Subgroup ↥X).Normal := Subgroup.normalizer_eq_top_iff.1 hNtop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup ↥X) with h | h
    · rw [hPY] at h
      rw [h, Subgroup.card_bot] at hcY'
      norm_num at hcY'
    · rw [hPY] at h
      rw [h, Subgroup.card_top, hX] at hcY'
      norm_num at hcY'
  set N := Subgroup.normalizer (P : Set ↥X) with hN
  have hmemP : ∀ h : ↥X, h ∈ (P : Set ↥X) ↔ h ∈ Y' := fun h => by rw [← hPY]; rfl
  have hNcard : Nat.card N * N.index = 168 := by rw [N.card_mul_index, hX]
  have heven : 2 ∣ Nat.card N := by
    have hmod' : Nat.card (Sylow 3 ↥X) % 3 = 1 := hmod
    have hmem : Nat.card (Sylow 3 ↥X) ∈ Nat.divisors 56 :=
      Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
    have hcases : N.index = 4 ∨ N.index = 7 ∨ N.index = 28 := by
      rw [← hn]
      have : Nat.divisors 56 = {1, 2, 4, 7, 8, 14, 28, 56} := by decide
      rw [this] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      omega
    rcases hcases with h | h | h <;> rw [h] at hNcard <;> omega
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 heven
  have ht2 : ((t : ↥X) : MulAut V) ^ 2 = 1 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe] at ht
    rw [← ht, pow_orderOf_eq_one]
  have ht1 : ((t : ↥X) : MulAut V) ≠ 1 := by
    intro h
    have : t = 1 := Subtype.ext (Subtype.ext h)
    rw [this, orderOf_one] at ht
    norm_num at ht
  refine ⟨((t : ↥X) : MulAut V), ⟨(t : ↥X).2, ?_⟩, fun htU => ht1 (hodd _ (t : ↥X).2 htU ht2),
    ht2⟩
  show ((t : ↥X) : MulAut V) ∈ Subgroup.normalizer (Y : Set (MulAut V))
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have htN0 : (t : ↥X) ∈ Subgroup.normalizer (P : Set ↥X) := t.2
  have htN : ∀ h : ↥X, h ∈ (P : Set ↥X) ↔ (t : ↥X) * h * (t : ↥X)⁻¹ ∈ (P : Set ↥X) :=
    fun h => htN0 h
  constructor
  · intro hh
    have h1 := (htN ⟨h, hYX hh⟩).1 ((hmemP _).2 hh)
    exact (hmemP _).1 h1
  · intro hh
    have hhX : h ∈ X := by
      have h2 : ((t : ↥X) : MulAut V) * h * ((t : ↥X) : MulAut V)⁻¹ ∈ X := hYX hh
      have h3 : h = ((t : ↥X) : MulAut V)⁻¹ *
          (((t : ↥X) : MulAut V) * h * ((t : ↥X) : MulAut V)⁻¹) * ((t : ↥X) : MulAut V) := by
        group
      rw [h3]
      exact X.mul_mem (X.mul_mem (X.inv_mem (t : ↥X).2) h2) (t : ↥X).2
    have h1 := (htN ⟨h, hhX⟩).2 ((hmemP _).2 hh)
    exact (hmemP _).1 h1

end L3Hyp

namespace S1248

variable {G : Type} [Group G] {L V U : Subgroup G} [IsMulCommutative ↥V]

@[expose] noncomputable def actHom (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    ↥L →* ↥(autOn L V) :=
  (A4.actionOn V L hLV).codRestrict (autOn L V) fun l => (A4.mem_autOn_iff hLV).mpr ⟨l, rfl⟩

omit [IsMulCommutative ↥V] in
theorem actHom_coe_apply (hLV : L ≤ Subgroup.normalizer (V : Set G)) (l : ↥L) (v : ↥V) :
    ((((actHom hLV l : ↥(autOn L V)) : MulAut ↥V) v : ↥V) : G) = l * v * (l : G)⁻¹ := rfl

omit [IsMulCommutative ↥V] in
theorem actHom_surjective (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    Function.Surjective (actHom hLV) := by
  rintro ⟨a, ha⟩
  obtain ⟨l, rfl⟩ := (A4.mem_autOn_iff hLV).mp ha
  exact ⟨l, rfl⟩

omit [IsMulCommutative ↥V] in
theorem mem_ker_actHom (hLV : L ≤ Subgroup.normalizer (V : Set G)) (l : ↥L) :
    l ∈ (actHom hLV).ker ↔ (l : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    exact (A4.actionOn_eq_one_iff hLV l).mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((A4.actionOn_eq_one_iff hLV l).mpr h)

theorem actHom_mem_stabSub_iff (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hUV : U ≤ V)
    (l : ↥L) : ((actHom hLV l : ↥(autOn L V)) : MulAut ↥V) ∈ stabSub (U.subgroupOf V) ↔
      (l : G) ∈ Subgroup.normalizer (U : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro g
    by_cases hg : g ∈ V
    · have h1 := h ⟨g, hg⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, actHom_coe_apply] at h1
      exact h1.symm
    · have hgU : g ∉ U := fun h' => hg (hUV h')
      have hlg : (l : G) * g * (l : G)⁻¹ ∉ V := fun h' =>
        hg ((Subgroup.mem_normalizer_iff.1 (hLV l.2) g).2 h')
      exact iff_of_false hgU fun h' => hlg (hUV h')
  · intro h u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, actHom_coe_apply]
    exact (Subgroup.mem_normalizer_iff.1 h u).symm

theorem actHom_mem_centSub_iff (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hUV : U ≤ V)
    (l : ↥L) : ((actHom hLV l : ↥(autOn L V)) : MulAut ↥V) ∈ centSub (U.subgroupOf V) ↔
      (l : G) ∈ Subgroup.centralizer (U : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 := congrArg Subtype.val (h ⟨u, hUV hu⟩ (Subgroup.mem_subgroupOf.2 hu))
    rw [actHom_coe_apply] at h1
    calc u * (l : G) = l * u * (l : G)⁻¹ * l := by rw [h1]
      _ = l * u := by group
  · intro h u hu
    apply Subtype.ext
    rw [actHom_coe_apply]
    have h1 := Subgroup.mem_centralizer_iff.1 h u (Subgroup.mem_subgroupOf.1 hu)
    calc (l : G) * u * (l : G)⁻¹ = u * l * (l : G)⁻¹ := by rw [h1]
      _ = u := by group

omit [IsMulCommutative ↥V] in
theorem card_comap_actHom (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (Q : Subgroup (MulAut ↥V)) (hQ : Q ≤ autOn L V) :
    Nat.card ((Q.subgroupOf (autOn L V)).comap (actHom hLV)) =
      Nat.card Q * Nat.card (actHom hLV).ker := by
  set π := actHom hLV
  set H := (Q.subgroupOf (autOn L V)).comap π
  have hKH : π.ker ≤ H := fun k hk => by
    show π k ∈ Q.subgroupOf (autOn L V)
    rw [MonoidHom.mem_ker.1 hk]
    exact Subgroup.one_mem _
  have h1 : π.ker.relIndex H = Nat.card Q := by
    rw [← MonoidHom.comap_bot, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective (actHom_surjective hLV),
      Subgroup.relIndex_bot_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ).toEquiv
  have h2 := Subgroup.relIndex_mul_card π.ker H
  rw [inf_eq_left.2 hKH, h1] at h2
  exact h2.symm

omit [IsMulCommutative ↥V] in
theorem eq_one_of_mem_ker_of_pow (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hker : IsPGroup 2 (actHom hLV).ker) {y : ↥L} (hy : y ∈ (actHom hLV).ker) {n : ℕ}
    (hyn : y ^ 3 ^ n = 1) : y = 1 := by
  obtain ⟨b, hb⟩ := hker ⟨y, hy⟩
  have hb' : y ^ 2 ^ b = 1 := congrArg Subtype.val hb
  have h1 := orderOf_dvd_of_pow_eq_one hb'
  have h2 := orderOf_dvd_of_pow_eq_one hyn
  have hcop : Nat.Coprime (2 ^ b) (3 ^ n) := Nat.Coprime.pow b n (by norm_num)
  have h3 : orderOf y ∣ 1 := by
    have := Nat.dvd_gcd h1 h2
    rwa [hcop.gcd_eq_one] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem lift_hypX_two [Finite G] (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hUV : U ≤ V)
    (hker : IsPGroup 2 (actHom hLV).ker) {Yb : Subgroup (MulAut ↥V)}
    (hYb : Yb ≤ autOn L V ⊓ stabSub (U.subgroupOf V)) (hYb27 : Nat.card Yb = 27)
    (hYb3 : ∀ y ∈ Yb, y ^ 3 = 1) (hYbU : Yb ⊓ centSub (U.subgroupOf V) = ⊥) :
    ∃ Y : Subgroup G, Y ≤ L ⊓ Subgroup.normalizer (U : Set G) ∧ Nat.card Y = 27 ∧
      (∀ y ∈ Y, y ^ 3 = 1) ∧ Y ⊓ Subgroup.centralizer (U : Set G) = ⊥ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := actHom hLV
  have hYbA : Yb ≤ autOn L V := hYb.trans inf_le_left
  set H := (Yb.subgroupOf (autOn L V)).comap π with hH
  have hcard := card_comap_actHom hLV Yb hYbA
  rw [hYb27] at hcard
  obtain ⟨Y₀, hY₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥H) 3 (n := 3)
    (by rw [hcard]; exact Dvd.intro _ rfl)
  set Y₁ : Subgroup ↥L := Y₀.map H.subtype
  have hY₁ : Nat.card Y₁ = 27 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hY₀]
    norm_num
  have hY₁H : Y₁ ≤ H := Subgroup.map_subtype_le Y₀
  have hY₁p : IsPGroup 3 Y₁ := IsPGroup.of_card (n := 3) (by rw [hY₁]; norm_num)
  have hπY : ∀ y ∈ Y₁, ((π y : ↥(autOn L V)) : MulAut ↥V) ∈ Yb := fun y hy => hY₁H hy
  have hinj : ∀ y ∈ Y₁, y ∈ π.ker → y = 1 := by
    intro y hy hyk
    obtain ⟨n, hn⟩ := hY₁p ⟨y, hy⟩
    exact eq_one_of_mem_ker_of_pow hLV hker hyk (congrArg Subtype.val hn)
  refine ⟨Y₁.map L.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨y.2, (actHom_mem_stabSub_iff hLV hUV y).1 (hYb (hπY y hy)).2⟩
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hY₁]
  · rintro _ ⟨y, hy, rfl⟩
    have h1 : y ^ 3 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact Subtype.ext (hYb3 _ (hπY y hy))
    have h2 := hinj _ (Y₁.pow_mem hy 3) h1
    exact congrArg Subtype.val h2
  · refine eq_bot_iff.2 ?_
    rintro _ ⟨⟨y, hy, rfl⟩, hyU⟩
    have h1 : ((π y : ↥(autOn L V)) : MulAut ↥V) ∈ Yb ⊓ centSub (U.subgroupOf V) :=
      ⟨hπY y hy, (actHom_mem_centSub_iff hLV hUV y).2 hyU⟩
    rw [hYbU, Subgroup.mem_bot] at h1
    have h2 := hinj y hy (MonoidHom.mem_ker.2 (Subtype.ext h1))
    rw [Subgroup.mem_bot, h2]
    rfl

theorem exists_conj_of_card_three [Finite G] {H A B : Subgroup G} (hA : A ≤ H) (hB : B ≤ H)
    (hA3 : Nat.card A = 3) (hB3 : Nat.card B = 3) (h9 : ¬ 9 ∣ Nat.card H) :
    ∃ h ∈ H, ∀ b ∈ B, h * b * h⁻¹ ∈ A := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A' := A.subgroupOf H
  set B' := B.subgroupOf H
  have hA' : Nat.card A' = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, hA3]
  have hB' : Nat.card B' = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv, hB3]
  have hidx : ∀ K : Subgroup ↥H, Nat.card K = 3 → ¬ 3 ∣ K.index := by
    intro K hK hd
    apply h9
    have h := K.card_mul_index
    rw [hK] at h
    obtain ⟨m, hm⟩ := hd
    rw [← h, hm]
    exact ⟨m, by ring⟩
  have hpA : IsPGroup 3 A' := IsPGroup.of_card (n := 1) (by rw [hA', pow_one])
  have hpB : IsPGroup 3 B' := IsPGroup.of_card (n := 1) (by rw [hB', pow_one])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥H (hpB.toSylow (hidx B' hB'))
    (hpA.toSylow (hidx A' hA'))
  refine ⟨g, g.2, fun b hb => ?_⟩
  have h1 : (⟨b, hB hb⟩ : ↥H) ∈ B' := Subgroup.mem_subgroupOf.2 hb
  have h2 : g * ⟨b, hB hb⟩ * g⁻¹ ∈ ((g • hpB.toSylow (hidx B' hB') : Sylow 3 ↥H) :
      Subgroup ↥H) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ h1
  rw [hg] at h2
  exact Subgroup.mem_subgroupOf.1 h2

omit [IsMulCommutative ↥V] in
theorem mem_normalizer_of_conj_mem [Finite G] {X : Subgroup G} {l : G}
    (h : ∀ x ∈ X, l * x * l⁻¹ ∈ X) : l ∈ Subgroup.normalizer (X : Set G) := by
  classical
  let f : ↥X → ↥X := fun x => ⟨l * x * l⁻¹, h x x.2⟩
  have hf : Function.Injective f := fun x y hxy => by
    have h1 : l * (x : G) * l⁻¹ = l * y * l⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (by simpa using h1)
  have hfs : Function.Surjective f := Finite.injective_iff_surjective.1 hf
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => h g hg, fun hg => ?_⟩
  obtain ⟨x, hx⟩ := hfs ⟨l * g * l⁻¹, hg⟩
  have h1 : l * (x : G) * l⁻¹ = l * g * l⁻¹ := congrArg Subtype.val hx
  have h2 : (x : G) = g := by simpa using h1
  rw [← h2]
  exact x.2

theorem lift_hypX_one [Finite G] (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hUV : U ≤ V)
    (hker : IsPGroup 2 (actHom hLV).ker) {Xb : Subgroup (MulAut ↥V)}
    (hXb : Xb ≤ autOn L V ⊓ stabSub (U.subgroupOf V)) (hXb3 : Nat.card Xb = 3)
    (hXbU : ¬ Xb ≤ centSub (U.subgroupOf V)) {t : MulAut ↥V}
    (ht : t ∈ autOn L V ⊓ Subgroup.normalizer (Xb : Set (MulAut ↥V)))
    (htU : t ∉ stabSub (U.subgroupOf V)) (ht2 : t ^ 2 ∈ stabSub (U.subgroupOf V)) :
    ∃ X : Subgroup G, X ≤ L ⊓ Subgroup.normalizer (U : Set G) ∧ Nat.card X = 3 ∧
      ¬ X ≤ Subgroup.centralizer (U : Set G) ∧
      ∃ l ∈ L ⊓ Subgroup.normalizer (X : Set G), l ∉ Subgroup.normalizer (U : Set G) ∧
        l ^ 2 ∈ Subgroup.normalizer (U : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := actHom hLV
  have hXbA : Xb ≤ autOn L V := hXb.trans inf_le_left
  obtain ⟨xb, hxbX, hxb1⟩ : ∃ xb ∈ Xb, xb ≠ 1 := by
    by_contra h
    push Not at h
    have h0 : Xb = ⊥ := eq_bot_iff.2 fun x hx => (Subgroup.mem_bot).2 (h x hx)
    rw [h0, Subgroup.card_bot] at hXb3
    norm_num at hXb3
  have hxb3 : orderOf xb = 3 := by
    have hd : orderOf xb ∣ 3 := hXb3 ▸ Subgroup.orderOf_dvd_natCard Xb hxbX
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hxb1
    · exact h
  obtain ⟨l₁, hl₁⟩ := actHom_surjective hLV ⟨xb, hXbA hxbX⟩
  have hl₁3 : l₁ ^ 3 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hl₁]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hxb3, pow_orderOf_eq_one]
  obtain ⟨b, hb⟩ := hker ⟨l₁ ^ 3, hl₁3⟩
  have hb' : (l₁ ^ 3) ^ 2 ^ b = 1 := congrArg Subtype.val hb
  set x : ↥L := l₁ ^ 2 ^ b with hx
  have hx3 : x ^ 3 = 1 := by
    rw [hx, ← pow_mul, mul_comm, pow_mul, hb']
  have hπx : ((π x : ↥(autOn L V)) : MulAut ↥V) = xb ^ 2 ^ b := by
    rw [hx, map_pow, hl₁, Subgroup.coe_pow]
  have hπx1 : xb ^ 2 ^ b ≠ 1 := by
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hxb3] at h1
    have h2 : Nat.Coprime 3 (2 ^ b) := Nat.Coprime.pow_right b (by norm_num)
    have h3 : 3 ∣ 1 := by
      have := Nat.dvd_gcd (dvd_refl 3) h1
      rwa [h2.gcd_eq_one] at this
    norm_num at h3
  have hπxX : ((π x : ↥(autOn L V)) : MulAut ↥V) ∈ Xb := by
    rw [hπx]
    exact Xb.pow_mem hxbX _
  have hx1 : (x : G) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, map_one] at hπx
    exact hπx1 (by rw [← hπx]; rfl)
  have hxo : orderOf (x : G) = 3 :=
    orderOf_eq_prime (by rw [← Subgroup.coe_pow, hx3]; rfl) hx1
  set X : Subgroup G := Subgroup.zpowers (x : G) with hXdef
  have hX3 : Nat.card X = 3 := by rw [hXdef, Nat.card_zpowers, hxo]
  have hxN : (x : G) ∈ Subgroup.normalizer (U : Set G) :=
    (actHom_mem_stabSub_iff hLV hUV x).1 (hXb hπxX).2
  have hXbgen : Xb ≤ Subgroup.zpowers ((π x : ↥(autOn L V)) : MulAut ↥V) := by
    have hle : Subgroup.zpowers ((π x : ↥(autOn L V)) : MulAut ↥V) ≤ Xb :=
      Subgroup.zpowers_le.2 hπxX
    have hord : orderOf ((π x : ↥(autOn L V)) : MulAut ↥V) = 3 := by
      have hd : orderOf ((π x : ↥(autOn L V)) : MulAut ↥V) ∣ 3 :=
        hXb3 ▸ Subgroup.orderOf_dvd_natCard Xb hπxX
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
      · exact absurd (by rw [← hπx]; exact orderOf_eq_one_iff.1 h) hπx1
      · exact h
    have := Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hord, hXb3])
    rw [this]
  obtain ⟨l₀, hl₀⟩ := actHom_surjective hLV ⟨t, ht.1⟩
  set H : Subgroup ↥L := (Xb.subgroupOf (autOn L V)).comap π with hH
  set HG : Subgroup G := H.map L.subtype with hHG
  have hcardHG : Nat.card HG = 3 * Nat.card π.ker := by
    rw [hHG, Subgroup.card_map_of_injective L.subtype_injective, card_comap_actHom hLV Xb hXbA,
      hXb3]
  have h9 : ¬ 9 ∣ Nat.card HG := by
    obtain ⟨k, hk⟩ := hker.exists_card_eq
    rw [hcardHG, hk]
    intro h
    have h1 : 3 ∣ 2 ^ k := by
      obtain ⟨m, hm⟩ := h
      exact ⟨m, by omega⟩
    have h2 : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have h3 : 3 ∣ 1 := by
      have := Nat.dvd_gcd (dvd_refl 3) h1
      rwa [h2.gcd_eq_one] at this
    norm_num at h3
  have hmemHG : ∀ y : ↥L, ((π y : ↥(autOn L V)) : MulAut ↥V) ∈ Xb → (y : G) ∈ HG :=
    fun y hy => ⟨y, hy, rfl⟩
  have hXHG : X ≤ HG := Subgroup.zpowers_le.2 (hmemHG x hπxX)
  set X' : Subgroup G := Subgroup.zpowers ((l₀ : G) * x * (l₀ : G)⁻¹) with hX'def
  have hπx' : ((π (l₀ * x * l₀⁻¹) : ↥(autOn L V)) : MulAut ↥V) ∈ Xb := by
    rw [map_mul, map_mul, map_inv, hl₀]
    exact (Subgroup.mem_normalizer_iff.1 ht.2 _).1 hπxX
  have hX'HG : X' ≤ HG := Subgroup.zpowers_le.2 (hmemHG _ hπx')
  have hX'3 : Nat.card X' = 3 := by
    rw [hX'def, Nat.card_zpowers]
    have : orderOf ((l₀ : G) * x * (l₀ : G)⁻¹) = orderOf (x : G) := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    rw [this, hxo]
  obtain ⟨p, hpHG, hp⟩ := exists_conj_of_card_three hXHG hX'HG hX3 hX'3 h9
  obtain ⟨p', hp'H, rfl⟩ := hpHG
  refine ⟨X, fun y hy => ⟨Subgroup.zpowers_le.2 x.2 hy, Subgroup.zpowers_le.2 hxN hy⟩, hX3,
    fun hXC => ?_, (p' * l₀ : ↥L), ⟨(p' * l₀).2, ?_⟩, ?_, ?_⟩
  ·
    apply hXbU
    refine hXbgen.trans (Subgroup.zpowers_le.2 ?_)
    exact (actHom_mem_centSub_iff hLV hUV x).2 (hXC (Subgroup.mem_zpowers _))
  ·
    apply mem_normalizer_of_conj_mem
    intro y hy
    have h1 : (l₀ : G) * y * (l₀ : G)⁻¹ ∈ X' := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      refine ⟨k, ?_⟩
      show ((l₀ : G) * x * (l₀ : G)⁻¹) ^ k = l₀ * (x : G) ^ k * (l₀ : G)⁻¹
      rw [← MulAut.conj_apply, ← map_zpow, MulAut.conj_apply]
    have h2 := hp _ h1
    show ((p' : G) * l₀) * y * ((p' : G) * l₀)⁻¹ ∈ X
    have e : ((p' : G) * l₀) * y * ((p' : G) * l₀)⁻¹ =
        (p' : G) * ((l₀ : G) * y * (l₀ : G)⁻¹) * (p' : G)⁻¹ := by group
    rw [e]
    exact h2
  ·
    intro hl
    have h1 := (actHom_mem_stabSub_iff hLV hUV (p' * l₀)).2 hl
    rw [map_mul, hl₀, Subgroup.coe_mul] at h1
    have h2 : ((π p' : ↥(autOn L V)) : MulAut ↥V) ∈ stabSub (U.subgroupOf V) := (hXb hp'H).2
    apply htU
    have e : t = ((π p' : ↥(autOn L V)) : MulAut ↥V)⁻¹ *
        (((π p' : ↥(autOn L V)) : MulAut ↥V) * t) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h2) h1
  ·
    have hl2 : (((p' * l₀ : ↥L) : G) ^ 2) = (((p' * l₀) ^ 2 : ↥L) : G) := rfl
    rw [hl2]
    apply (actHom_mem_stabSub_iff hLV hUV _).1
    rw [map_pow, map_mul, hl₀, Subgroup.coe_pow, Subgroup.coe_mul]
    set q : MulAut ↥V := ((π p' : ↥(autOn L V)) : MulAut ↥V) with hq
    have hqX : q ∈ Xb := hp'H
    have htq : t * q * t⁻¹ ∈ Xb := (Subgroup.mem_normalizer_iff.1 ht.2 q).1 hqX
    have e : (q * t) ^ 2 = q * (t * q * t⁻¹) * t ^ 2 := by rw [sq, sq]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hXb hqX).2 (hXb htq).2) ht2

omit [IsMulCommutative ↥V] in
theorem isPGroup_ker_actHom [Finite G] (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G))
    (hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) (hnc : ¬ L ≤ Subgroup.centralizer (V : Set G)) :
    IsPGroup 2 (actHom hLV).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eA⟩ := nonempty_autOn_mulEquiv_quotient hLV hO2 hs hnc
  have hinj : Function.Injective (autOnQuot hLV hO2) :=
    (Finite.injective_iff_surjective_of_equiv eA.symm.toEquiv).2 (autOnQuot_surjective hLV hO2)
  have hle : (actHom hLV).ker ≤ CFSG.pCore 2 ↥L := by
    intro l hl
    have hl' : l ∈ (autOnSurj hLV).ker := (mem_ker_autOnSurj hLV l).2 ((mem_ker_actHom hLV l).1 hl)
    have h1 : autOnQuot hLV hO2 (QuotientGroup.mk l) = 1 := by
      rw [autOnQuot_mk]
      exact hl'
    have h2 : (QuotientGroup.mk l : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 :=
      hinj (h1.trans (map_one _).symm)
    exact (QuotientGroup.eq_one_iff l).1 h2
  exact (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).to_le hle

omit [IsMulCommutative ↥V] in
theorem conjAct_coe_apply (g : ↥(Subgroup.normalizer (V : Set G))) (v : ↥V) :
    ((conjAct V g v : ↥V) : G) = g * v * (g : G)⁻¹ := rfl

theorem conjAct_mem_stabSub_iff (hUV : U ≤ V) (g : ↥(Subgroup.normalizer (V : Set G))) :
    conjAct V g ∈ stabSub (U.subgroupOf V) ↔ (g : G) ∈ Subgroup.normalizer (U : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro x
    by_cases hx : x ∈ V
    · have h1 := h ⟨x, hx⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, conjAct_coe_apply] at h1
      exact h1.symm
    · have hxU : x ∉ U := fun h' => hx (hUV h')
      have hgx : (g : G) * x * (g : G)⁻¹ ∉ V := fun h' =>
        hx ((Subgroup.mem_normalizer_iff.1 g.2 x).2 h')
      exact iff_of_false hxU fun h' => hgx (hUV h')
  · intro h u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, conjAct_coe_apply]
    exact (Subgroup.mem_normalizer_iff.1 h u).symm

theorem lift_hypX_one_of_normalizer [Finite G] (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hUV : U ≤ V) (hker : IsPGroup 2 (actHom hLV).ker) {H : Subgroup G}
    (hHL : H ≤ Subgroup.normalizer (L : Set G)) (hHV : H ≤ Subgroup.normalizer (V : Set G))
    {Xb : Subgroup (MulAut ↥V)}
    (hXb : Xb ≤ autOn L V ⊓ stabSub (U.subgroupOf V)) (hXb3 : Nat.card Xb = 3)
    (hXbU : ¬ Xb ≤ centSub (U.subgroupOf V)) {t : MulAut ↥V}
    (ht : t ∈ autOn H V ⊓ Subgroup.normalizer (Xb : Set (MulAut ↥V)))
    (htU : t ∉ stabSub (U.subgroupOf V)) (ht2 : t ^ 2 ∈ stabSub (U.subgroupOf V)) :
    ∃ X : Subgroup G, X ≤ L ⊓ Subgroup.normalizer (U : Set G) ∧ Nat.card X = 3 ∧
      ¬ X ≤ Subgroup.centralizer (U : Set G) ∧
      ∃ l ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (X : Set G),
        l ∉ Subgroup.normalizer (U : Set G) ∧ l ^ 2 ∈ Subgroup.normalizer (U : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := actHom hLV
  have hXbA : Xb ≤ autOn L V := hXb.trans inf_le_left
  obtain ⟨xb, hxbX, hxb1⟩ : ∃ xb ∈ Xb, xb ≠ 1 := by
    by_contra h
    push Not at h
    have h0 : Xb = ⊥ := eq_bot_iff.2 fun x hx => (Subgroup.mem_bot).2 (h x hx)
    rw [h0, Subgroup.card_bot] at hXb3
    norm_num at hXb3
  have hxb3 : orderOf xb = 3 := by
    have hd : orderOf xb ∣ 3 := hXb3 ▸ Subgroup.orderOf_dvd_natCard Xb hxbX
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hxb1
    · exact h
  obtain ⟨l₁, hl₁⟩ := actHom_surjective hLV ⟨xb, hXbA hxbX⟩
  have hl₁3 : l₁ ^ 3 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hl₁]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hxb3, pow_orderOf_eq_one]
  obtain ⟨b, hb⟩ := hker ⟨l₁ ^ 3, hl₁3⟩
  have hb' : (l₁ ^ 3) ^ 2 ^ b = 1 := congrArg Subtype.val hb
  set x : ↥L := l₁ ^ 2 ^ b with hx
  have hx3 : x ^ 3 = 1 := by
    rw [hx, ← pow_mul, mul_comm, pow_mul, hb']
  have hπx : ((π x : ↥(autOn L V)) : MulAut ↥V) = xb ^ 2 ^ b := by
    rw [hx, map_pow, hl₁, Subgroup.coe_pow]
  have hπx1 : xb ^ 2 ^ b ≠ 1 := by
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hxb3] at h1
    have h2 : Nat.Coprime 3 (2 ^ b) := Nat.Coprime.pow_right b (by norm_num)
    have h3 : 3 ∣ 1 := by
      have := Nat.dvd_gcd (dvd_refl 3) h1
      rwa [h2.gcd_eq_one] at this
    norm_num at h3
  have hπxX : ((π x : ↥(autOn L V)) : MulAut ↥V) ∈ Xb := by
    rw [hπx]
    exact Xb.pow_mem hxbX _
  have hx1 : (x : G) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, map_one] at hπx
    exact hπx1 (by rw [← hπx]; rfl)
  have hxo : orderOf (x : G) = 3 :=
    orderOf_eq_prime (by rw [← Subgroup.coe_pow, hx3]; rfl) hx1
  set X : Subgroup G := Subgroup.zpowers (x : G) with hXdef
  have hX3 : Nat.card X = 3 := by rw [hXdef, Nat.card_zpowers, hxo]
  have hxN : (x : G) ∈ Subgroup.normalizer (U : Set G) :=
    (actHom_mem_stabSub_iff hLV hUV x).1 (hXb hπxX).2
  have hXbgen : Xb ≤ Subgroup.zpowers ((π x : ↥(autOn L V)) : MulAut ↥V) := by
    have hle : Subgroup.zpowers ((π x : ↥(autOn L V)) : MulAut ↥V) ≤ Xb :=
      Subgroup.zpowers_le.2 hπxX
    have hord : orderOf ((π x : ↥(autOn L V)) : MulAut ↥V) = 3 := by
      have hd : orderOf ((π x : ↥(autOn L V)) : MulAut ↥V) ∣ 3 :=
        hXb3 ▸ Subgroup.orderOf_dvd_natCard Xb hπxX
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
      · exact absurd (by rw [← hπx]; exact orderOf_eq_one_iff.1 h) hπx1
      · exact h
    have := Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hord, hXb3])
    rw [this]
  obtain ⟨h₀, hh₀⟩ := (A4.mem_autOn_iff hHV).mp ht.1
  have hh₀L : (h₀ : G) * x * (h₀ : G)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.1 (hHL h₀.2) x).1 x.2
  set x' : ↥L := ⟨(h₀ : G) * x * (h₀ : G)⁻¹, hh₀L⟩ with hx'def
  have hcomm : ((π x' : ↥(autOn L V)) : MulAut ↥V) * t =
      t * ((π x : ↥(autOn L V)) : MulAut ↥V) := by
    rw [← hh₀]
    ext v
    show (((π x' : ↥(autOn L V)) : MulAut ↥V) (A4.actionOn V H hHV h₀ v) : G) =
      ((A4.actionOn V H hHV h₀ (((π x : ↥(autOn L V)) : MulAut ↥V) v) : ↥V) : G)
    rw [actHom_coe_apply, A4.actionOn_apply_coe, A4.actionOn_apply_coe, actHom_coe_apply]
    simp only [hx'def]
    group
  have hπx' : ((π x' : ↥(autOn L V)) : MulAut ↥V) ∈ Xb := by
    have e : ((π x' : ↥(autOn L V)) : MulAut ↥V) =
        t * ((π x : ↥(autOn L V)) : MulAut ↥V) * t⁻¹ := eq_mul_inv_of_mul_eq hcomm
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 ht.2 _).1 hπxX
  set HL : Subgroup ↥L := (Xb.subgroupOf (autOn L V)).comap π with hHL'
  set HG : Subgroup G := HL.map L.subtype with hHG
  have hcardHG : Nat.card HG = 3 * Nat.card π.ker := by
    rw [hHG, Subgroup.card_map_of_injective L.subtype_injective, card_comap_actHom hLV Xb hXbA,
      hXb3]
  have h9 : ¬ 9 ∣ Nat.card HG := by
    obtain ⟨k, hk⟩ := hker.exists_card_eq
    rw [hcardHG, hk]
    intro h
    have h1 : 3 ∣ 2 ^ k := by
      obtain ⟨m, hm⟩ := h
      exact ⟨m, by omega⟩
    have h2 : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have h3 : 3 ∣ 1 := by
      have := Nat.dvd_gcd (dvd_refl 3) h1
      rwa [h2.gcd_eq_one] at this
    norm_num at h3
  have hmemHG : ∀ y : ↥L, ((π y : ↥(autOn L V)) : MulAut ↥V) ∈ Xb → (y : G) ∈ HG :=
    fun y hy => ⟨y, hy, rfl⟩
  have hXHG : X ≤ HG := Subgroup.zpowers_le.2 (hmemHG x hπxX)
  set X' : Subgroup G := Subgroup.zpowers ((h₀ : G) * x * (h₀ : G)⁻¹) with hX'def
  have hX'HG : X' ≤ HG := Subgroup.zpowers_le.2 (hmemHG x' hπx')
  have hX'3 : Nat.card X' = 3 := by
    rw [hX'def, Nat.card_zpowers]
    have : orderOf ((h₀ : G) * x * (h₀ : G)⁻¹) = orderOf (x : G) := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    rw [this, hxo]
  obtain ⟨p, hpHG, hp⟩ := exists_conj_of_card_three hXHG hX'HG hX3 hX'3 h9
  obtain ⟨p', hp'H, rfl⟩ := hpHG
  have hlV : (p' : G) * h₀ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (hLV p'.2) (hHV h₀.2)
  have hlact : conjAct V ⟨(p' : G) * h₀, hlV⟩ =
      ((π p' : ↥(autOn L V)) : MulAut ↥V) * t := by
    rw [← hh₀]
    ext v
    show ((p' : G) * h₀) * v * ((p' : G) * h₀)⁻¹ =
      ((((π p' : ↥(autOn L V)) : MulAut ↥V) (A4.actionOn V H hHV h₀ v) : ↥V) : G)
    rw [actHom_coe_apply, A4.actionOn_apply_coe]
    group
  have hq : ((π p' : ↥(autOn L V)) : MulAut ↥V) ∈ Xb := hp'H
  refine ⟨X, fun y hy => ⟨Subgroup.zpowers_le.2 x.2 hy, Subgroup.zpowers_le.2 hxN hy⟩, hX3,
    fun hXC => ?_, (p' : G) * h₀, ⟨hlV, ?_⟩, ?_, ?_⟩
  ·
    apply hXbU
    refine hXbgen.trans (Subgroup.zpowers_le.2 ?_)
    exact (actHom_mem_centSub_iff hLV hUV x).2 (hXC (Subgroup.mem_zpowers _))
  ·
    apply mem_normalizer_of_conj_mem
    intro y hy
    have h1 : (h₀ : G) * y * (h₀ : G)⁻¹ ∈ X' := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      refine ⟨k, ?_⟩
      show ((h₀ : G) * x * (h₀ : G)⁻¹) ^ k = h₀ * (x : G) ^ k * (h₀ : G)⁻¹
      rw [← MulAut.conj_apply, ← map_zpow, MulAut.conj_apply]
    have h2 := hp _ h1
    have e : ((p' : G) * h₀) * y * ((p' : G) * h₀)⁻¹ =
        (p' : G) * ((h₀ : G) * y * (h₀ : G)⁻¹) * (p' : G)⁻¹ := by group
    rw [e]
    exact h2
  ·
    intro hl
    have h1 := (conjAct_mem_stabSub_iff hUV ⟨(p' : G) * h₀, hlV⟩).2 hl
    rw [hlact] at h1
    apply htU
    have e : t = ((π p' : ↥(autOn L V)) : MulAut ↥V)⁻¹ *
        (((π p' : ↥(autOn L V)) : MulAut ↥V) * t) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hXb hq).2) h1
  ·
    have hl2V : ((p' : G) * h₀) ^ 2 ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.pow_mem _ hlV 2
    apply (conjAct_mem_stabSub_iff hUV ⟨((p' : G) * h₀) ^ 2, hl2V⟩).1
    have e2 : (⟨((p' : G) * h₀) ^ 2, hl2V⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨(p' : G) * h₀, hlV⟩ ^ 2 := rfl
    rw [e2, map_pow, hlact]
    set q : MulAut ↥V := ((π p' : ↥(autOn L V)) : MulAut ↥V) with hqdef
    have htq : t * q * t⁻¹ ∈ Xb := (Subgroup.mem_normalizer_iff.1 ht.2 q).1 hq
    have e : (q * t) ^ 2 = q * (t * q * t⁻¹) * t ^ 2 := by rw [sq, sq]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hXb hq).2 (hXb htq).2) ht2

variable {T : Subgroup G} {z : G}

theorem exists_offender_autOn_T [Finite G] (h1229 : Stmt12_2_9) (hpre : Pre1242)
    (hcx : Cx1242 G T L V) (hf : CxFacts G T L V z) :
    ∃ B : Subgroup G, B ≤ T ∧ autOn B V ≠ ⊥ ∧ IsElemAbelian2 (autOn B V) ∧
      Nat.card ↥V ≤ Nat.card (autOn B V) * Nat.card (fixV (autOn B V)) := by
  have hJ : L = ⁅L, thompsonJ T⁆ :=
    lemma12_4_3_two_of h1229 (lemma12_4_3_one_of_pre hpre) G T L V hcx
  obtain ⟨B, hB, hBV⟩ : ∃ B : Subgroup G, IsMaxElemAbelian T B ∧
      ¬ B ≤ Subgroup.centralizer (V : Set G) := by
    by_contra hall
    push Not at hall
    have hJV : thompsonJ T ≤ Subgroup.centralizer (V : Set G) := iSup₂_le fun B hB => hall B hB
    apply hf.notCent
    rw [hJ, Subgroup.commutator_le]
    intro l hl j hj
    have hjN : j ∈ Subgroup.normalizer (V : Set G) :=
      hf.T_le ((iSup₂_le fun B (hB : IsMaxElemAbelian T B) => hB.1 : thompsonJ T ≤ T) hj)
    have hj1 : conjAct V ⟨j, hjN⟩ = 1 := A4.conjAct_eq_one_iff.2 (hJV hj)
    have h1 : conjAct V ⁅(⟨l, hf.normalizes hl⟩ : Subgroup.normalizer (V : Set G)),
        ⟨j, hjN⟩⁆ = 1 := by
      rw [map_commutatorElement, hj1, commutatorElement_one_right]
    exact A4.conjAct_eq_one_iff.1 h1
  have hBT : B ≤ T := hB.1
  have hBN : B ≤ Subgroup.normalizer (V : Set G) := hBT.trans hf.T_le
  have hB1 : autOn B V ≠ ⊥ := by
    intro h
    apply hBV
    intro b hb
    have h1 : conjAct V ⟨b, hBN hb⟩ ∈ autOn B V :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hb)
    rw [h, Subgroup.mem_bot] at h1
    exact A4.conjAct_eq_one_iff.1 h1
  have hr : Nat.card ↥V ≤ Nat.card (autOn B V) * Nat.card (fixV (autOn B V)) := by
    have h1 := card_le_relIndex_mul_card hf.isElemAbelian hf.le_T hB
    rwa [← card_autOn_eq_relIndex hBN, ← card_subgroupOf_eq_card_inf,
      ← fixV_autOn_eq hBN] at h1
  exact ⟨B, hBT, hB1, isElemAbelian2_autOn' hB.2.1, hr⟩

theorem autOn_T_not_le [Finite G] (h1229 : Stmt12_2_9) (hpre : Pre1242)
    (hcx : Cx1242 G T L V) (hf : CxFacts G T L V z) (hoff : G2DerivedNoOffender1248)
    (hW : ∀ w : ↥V, w ^ 2 = 1) (hcomm : commV (autOn L V) = ⊤)
    (hfix : Nat.card (fixV (autOn L V)) = 2)
    (hnat : G2NaturalDerived (autOn L V) ⊤ (fixV (autOn L V)) 1) :
    ¬ autOn T V ≤ autOn L V := by
  intro hTL
  obtain ⟨B, hBT, hB1, hBe, hr⟩ := exists_offender_autOn_T h1229 hpre hcx hf
  exact hoff ↥V hW (autOn L V) hcomm hfix hnat (autOn B V) ((A4.autOn_mono hBT).trans hTL) hB1
    hBe hr

end S1248

open S1248

theorem hypX1248_of_outer
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1229 : Stmt12_2_9) (hpre : Pre1242)
    (hoff : G2DerivedNoOffender1248) (hG2 : G2HypXFact1248) : HypX1248 := by
  intro G _ _ T L V U hS
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hS.cx.hyp
  obtain ⟨z, hf⟩ := CxFacts.of h331 h1222 hpre hS.cx hS.quot
  obtain ⟨_, hcases⟩ := modules_cases_of_hyp1223 h1222 hyp
  have := hf.comm
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hf.normalizes
  have hW : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hf.sq w w.2)
  have hZ2 : Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) = 2 := by
    rw [hf.zV, Nat.card_zpowers, hf.order]
  have hcommGr : commV (autOn L V) = ⊤ := commV_autOn_eq_top hLV hf.commutator
  have hfixGr : Nat.card (fixV (autOn L V)) = 2 := by
    rw [fixV_autOn_eq hLV, card_subgroupOf_eq_card_inf, hZ2]
  have hU' : (U.subgroupOf V).index = 2 := hS.hyper
  have hzU : z ∉ U := by
    intro hzU
    apply hS.escape
    rw [← hf.MN, hf.MC]
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzU)
  have hnot : ¬ fixV (autOn L V) ≤ U.subgroupOf V := by
    intro h
    rw [fixV_autOn_eq hLV] at h
    have hz : (⟨z, hf.mem_zV.1⟩ : ↥V) ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V :=
      Subgroup.mem_subgroupOf.2 hf.mem_zV.2
    exact hzU (Subgroup.mem_subgroupOf.1 (h hz))
  have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases hS.quot with h3 | hU
    · obtain ⟨e⟩ := h3
      have := (isSimpleGroup_sl_zmod_two (m := 3) (by norm_num)).1
      exact e.isSimpleGroup
    · exact CFSG.Timmesfeld.isSimpleGroup_of_lieModel hU
  have hker := isPGroup_ker_actHom hLV hf.pCore hs hf.notCent
  rcases hS.quot with h3 | hU
  ·
    obtain ⟨e⟩ := h3
    have h168 := card_quot_of_sl_three ⟨e⟩
    obtain ⟨eA⟩ := nonempty_autOn_mulEquiv_quotient hLV hf.pCore hs hf.notCent
    have hGrs : IsSimpleGroup (autOn L V) := eA.isSimpleGroup
    have hGr : Nat.card (autOn L V) = 168 := by rw [Nat.card_congr eA.toEquiv, h168]
    have hV16 : Nat.card V = 2 ^ 4 :=
      le_antisymm (hcases.1 ⟨e⟩) (by
        have := sixteen_le_card_V h331 h1222 hpre hS.cx hS.quot
        norm_num
        exact this)
    obtain ⟨Y, hY, hY3, hYU, t, ht, htU, ht2⟩ :=
      L3Hyp.exists_hypX hW hV16 (autOn L V) hGrs hGr hcommGr hfixGr (U.subgroupOf V) hU' hnot
    left
    obtain ⟨X, hX, hX3, hXU, l, hl, hlU, hl2⟩ :=
      lift_hypX_one hLV hS.le hker hY hY3 hYU ht htU (by rw [ht2]; exact Subgroup.one_mem _)
    exact ⟨X, hX, hX3, hXU, l, ⟨hLV hl.1, hl.2⟩, hlU, hl2⟩
  ·
    have hnat : G2NaturalDerived (autOn L V) ⊤ (fixV (autOn L V)) 1 := by
      rw [fixV_autOn_eq hLV]
      exact hcases.2.1 hU
    have hTL : T ≤ Subgroup.normalizer (L : Set G) := by
      rw [hf.MN]
      exact hf.T_le
    have hLTL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
    have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hf.T_le
    have hlt : autOn L V < autOn (L ⊔ T) V := by
      refine lt_of_le_of_ne (A4.autOn_mono le_sup_left) fun heq => ?_
      refine autOn_T_not_le h1229 hpre hS.cx hf hoff hW hcommGr hfixGr hnat ?_
      rw [heq]
      exact A4.autOn_mono le_sup_right
    rcases hG2 ↥V hW (autOn L V) hcommGr hfixGr hnat (autOn (L ⊔ T) V) hlt
        (autOn_le_normalizer_autOn_of_le hLTL) (U.subgroupOf V) hU' hnot with
      ⟨Xb, hXb, hXb3, hXbU, t, ht, htU, ht2⟩ | ⟨Yb, hYb, hYb27, hYb3, hYbU⟩
    · left
      exact lift_hypX_one_of_normalizer hLV hS.le hker hLTL hLTV hXb hXb3 hXbU ht htU ht2
    · right
      exact lift_hypX_two hLV hS.le hker hYb hYb27 hYb3 hYbU

end CFSG.Quasithin.H13
