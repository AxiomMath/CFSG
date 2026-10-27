module

public import CFSG.RankThree.PartTwo.Sec10.Item10Std
import TauCeti.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringU3n

open CFSG CFSG.ABGLocalTools

section Lift

variable {G : Type} [Group G] [Finite G] {K N : Subgroup G} {H : Type} [Group H] [Finite H]

theorem factorization_two_mul {a b m : ℕ} (ha : Odd a) (hb : Odd b) :
    (a * (2 ^ m * b)).factorization 2 = m := by
  have ha0 : a ≠ 0 := ha.pos.ne'
  have hb0 : b ≠ 0 := hb.pos.ne'
  rw [Nat.factorization_mul ha0 (mul_ne_zero (pow_ne_zero _ two_ne_zero) hb0), Finsupp.add_apply,
    Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hb0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (Nat.odd_iff.mp ha |> fun h => by omega),
    Nat.factorization_eq_zero_of_not_dvd (Nat.odd_iff.mp hb |> fun h => by omega)]
  simp

variable (φ : K →* H)

@[expose] def img (Z : Subgroup G) : Subgroup H := (Z.subgroupOf K).map φ

theorem mem_img {Z : Subgroup G} {h : H} :
    h ∈ img φ Z ↔ ∃ z : K, (z : G) ∈ Z ∧ φ z = h := by
  unfold img
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, Subgroup.mem_subgroupOf.mp hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, Subgroup.mem_subgroupOf.mpr hz, rfl⟩

theorem inj_on_two_group (hN : ∀ x : K, φ x = 1 ↔ (x : G) ∈ N) (hNodd : Odd (Nat.card N))
    {Z : Subgroup G} (hZ : IsPGroup 2 Z) {x y : K} (hx : (x : G) ∈ Z) (hy : (y : G) ∈ Z)
    (hxy : φ x = φ y) : x = y := by
  have h1 : φ (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have hmem : ((x⁻¹ * y : K) : G) ∈ N := (hN _).mp h1
  have hZmem : ((x⁻¹ * y : K) : G) ∈ Z := Z.mul_mem (Z.inv_mem hx) hy
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN2 : ¬ 2 ∣ Nat.card N := by
    have := Nat.odd_iff.mp hNodd
    omega
  have hbot : Z ⊓ N = ⊥ := by
    rw [inf_comm]
    exact disjoint_iff.mp (TauCeti.disjoint_of_not_dvd_natCard_of_isPGroup hN2 hZ)
  have hmem' : ((x⁻¹ * y : K) : G) ∈ Z ⊓ N := ⟨hZmem, hmem⟩
  rw [hbot, Subgroup.mem_bot] at hmem'
  exact inv_mul_eq_one.mp (Subtype.ext hmem')

theorem card_img (hN : ∀ x : K, φ x = 1 ↔ (x : G) ∈ N) (hNodd : Odd (Nat.card N))
    {Z : Subgroup G} (hZK : Z ≤ K) (hZ : IsPGroup 2 Z) : Nat.card (img φ Z) = Nat.card Z := by
  let f : Z.subgroupOf K → img φ Z := fun z =>
    ⟨φ z, (mem_img φ).mpr ⟨z, Subgroup.mem_subgroupOf.mp z.2, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro z z' h
    apply Subtype.ext
    exact inj_on_two_group φ hN hNodd hZ (Subgroup.mem_subgroupOf.mp z.2)
      (Subgroup.mem_subgroupOf.mp z'.2) (congrArg Subtype.val h)
  have hsurj : Function.Surjective f := by
    rintro ⟨h, hh⟩
    obtain ⟨z, hz, rfl⟩ := (mem_img φ).mp hh
    exact ⟨⟨z, Subgroup.mem_subgroupOf.mpr hz⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv

theorem exists_lift_sylow (hφ : Function.Surjective φ)
    (hN : ∀ x : K, φ x = 1 ↔ (x : G) ∈ N) (hNK : N ≤ K)
    (hNodd : Odd (Nat.card N)) (hN3 : ¬ 3 ∣ Nat.card N)
    {m r : ℕ} (hr : Odd r) (hH : Nat.card H = 2 ^ m * r)
    (hElem : ∀ U : Subgroup H, Nat.card U = 2 ^ m → ∀ x ∈ U, ∀ y ∈ U,
      x * y = y * x ∧ x ^ 2 = 1)
    (hTI : ∀ U U' : Subgroup H, Nat.card U = 2 ^ m → Nat.card U' = 2 ^ m →
      ∀ x ∈ U, x ∈ U' → x ≠ 1 → U = U')
    (hTrans : ∀ U : Subgroup H, Nat.card U = 2 ^ m → ∀ u ∈ U, u ≠ 1 → ∀ v ∈ U, v ≠ 1 →
      ∃ n ∈ Subgroup.normalizer (U : Set H), n * u * n⁻¹ = v)
    {E T : Subgroup G} (hE3 : IsPGroup 3 E) (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hEN : E ≤ Subgroup.normalizer (N : Set G))
    (hTK : T ≤ K) (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hET : E ≤ Subgroup.normalizer (T : Set G)) :
    ∃ S : Subgroup G, S ≤ K ∧ Nat.card S = 2 ^ m ∧ CFSG.Assembly.IsElemAbelian 2 S ∧
      E ≤ Subgroup.normalizer (S : Set G) ∧
      ∀ u ∈ S, u ≠ 1 → ∀ v ∈ S, v ≠ 1 → ∃ n ∈ Subgroup.normalizer (S : Set G),
        n * u * n⁻¹ = v := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hker : φ.ker = N.subgroupOf K := by
    ext x
    rw [MonoidHom.mem_ker, hN x]
    rfl
  have hkerN : Nat.card φ.ker = Nat.card N := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv
  have hrange : φ.range = ⊤ := MonoidHom.range_eq_top.mpr hφ
  have hKcard : Nat.card K = Nat.card N * (2 ^ m * r) := by
    have := Subgroup.card_ker_mul_card_range φ
    rw [hrange, Subgroup.card_top, hkerN, hH] at this
    exact this.symm
  have hK2 : (Nat.card K).factorization 2 = m := by
    rw [hKcard]
    exact factorization_two_mul hNodd hr
  have hT'2 : IsPGroup 2 (T.subgroupOf K) := hT2.comap_subtype
  obtain ⟨Q, hTQ⟩ := hT'2.exists_le_sylow
  set P0 : Subgroup G := (Q : Subgroup K).map K.subtype with hP0def
  have hP0 : IsSylowOf 2 P0 K := ⟨Q, rfl⟩
  have hP0K : P0 ≤ K := hP0.le
  have hP02 : IsPGroup 2 P0 := hP0.isPGroup
  have hP0card : Nat.card P0 = 2 ^ m := by rw [hP0.card_eq, hK2]
  have hTP0 : T ≤ P0 := fun x hx => ⟨⟨x, hTK hx⟩, hTQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  set U0 : Subgroup H := img φ P0 with hU0
  have hU0card : Nat.card U0 = 2 ^ m := by
    rw [hU0, card_img φ hN hNodd hP0K hP02, hP0card]
  obtain ⟨⟨t, htT⟩, ht1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hT1
  have ht1 : t ≠ 1 := fun h => ht1' (Subtype.ext h)
  have htK : t ∈ K := hTK htT
  have hφt : φ ⟨t, htK⟩ ≠ 1 := by
    intro h
    have := inj_on_two_group φ hN hNodd hT2 (x := ⟨t, htK⟩) (y := 1) htT T.one_mem
      (by rw [h, map_one])
    exact ht1 (congrArg Subtype.val this)
  have hφtU0 : φ ⟨t, htK⟩ ∈ U0 := (mem_img φ).mpr ⟨⟨t, htK⟩, hTP0 htT, rfl⟩
  set Y' : Subgroup K := U0.comap φ with hY'
  set Y : Subgroup G := Y'.map K.subtype with hYdef
  have hYK : Y ≤ K := Subgroup.map_subtype_le _
  have hmemY : ∀ y : K, (y : G) ∈ Y ↔ φ y ∈ U0 := by
    intro y
    constructor
    · rintro ⟨y', hy', hyy⟩
      have : y' = y := Subtype.ext hyy
      subst this
      exact hy'
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hNY : N ≤ Y := fun x hx =>
    (hmemY ⟨x, hNK hx⟩).mpr (by rw [(hN _).mpr hx]; exact U0.one_mem)
  have hYcard : Nat.card Y = Nat.card N * 2 ^ m := by
    have e1 : Nat.card Y = Nat.card Y' :=
      Nat.card_congr (Subgroup.equivMapOfInjective Y' K.subtype K.subtype_injective).toEquiv.symm
    have h1 := Subgroup.card_mul_index Y'
    have h2' := Subgroup.card_mul_index U0
    rw [hY', Subgroup.index_comap_of_surjective U0 hφ, hKcard] at h1
    rw [hU0card, hH] at h2'
    have hidx : U0.index = r := Nat.eq_of_mul_eq_mul_left (pow_pos two_pos m) h2'
    rw [hidx] at h1
    rw [e1]
    apply Nat.eq_of_mul_eq_mul_right hr.pos
    rw [h1]
    ring
  have hY2 : (Nat.card Y).factorization 2 = m := by
    rw [hYcard, show Nat.card N * 2 ^ m = Nat.card N * (2 ^ m * 1) by ring]
    exact factorization_two_mul hNodd odd_one
  have hEY : E ≤ Subgroup.normalizer (Y : Set G) := by
    intro e he
    have heK := hEK he
    have heN := hEN he
    have heT := hET he
    have heTinv := hET (E.inv_mem he)
    set P1 : Subgroup G := P0.map (MulAut.conj e).toMonoidHom with hP1
    have hmemP1 : ∀ x : G, x ∈ P1 ↔ e⁻¹ * x * e ∈ P0 := by
      intro x
      constructor
      · rintro ⟨p, hp, rfl⟩
        have : e⁻¹ * ((MulAut.conj e).toMonoidHom p) * e = p := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [this]
        exact hp
      · intro hx
        refine ⟨e⁻¹ * x * e, hx, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    have hP1K : P1 ≤ K := by
      rintro _ ⟨p, hp, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp heK p).mp (hP0K hp)
    have hTP1 : T ≤ P1 := by
      intro x hx
      refine (hmemP1 x).mpr (hTP0 ?_)
      have := (Subgroup.mem_normalizer_iff.mp heTinv x).mp hx
      simpa using this
    have hP12 : IsPGroup 2 P1 := hP02.map _
    have hP1card : Nat.card P1 = 2 ^ m := by
      rw [hP1, Subgroup.card_map_of_injective (MulAut.conj e).injective, hP0card]
    have hU1card : Nat.card (img φ P1) = 2 ^ m := by
      rw [card_img φ hN hNodd hP1K hP12, hP1card]
    have hU01 : U0 = img φ P1 :=
      hTI U0 (img φ P1) hU0card hU1card (φ ⟨t, htK⟩) hφtU0
        ((mem_img φ).mpr ⟨⟨t, htK⟩, hTP1 htT, rfl⟩) hφt
    apply Subgroup.mem_normalizer_fintype
    intro y hy
    have hyK : y ∈ K := hYK hy
    have hyU : φ ⟨y, hyK⟩ ∈ U0 := (hmemY ⟨y, hyK⟩).mp hy
    obtain ⟨p, hpP0, hpφ⟩ := (mem_img φ).mp hyU
    have hnN : (((⟨y, hyK⟩ * p⁻¹ : K)) : G) ∈ N := by
      refine (hN _).mp ?_
      rw [map_mul, map_inv, hpφ, mul_inv_cancel]
    have hx1 : e * (((⟨y, hyK⟩ * p⁻¹ : K)) : G) * e⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp heN _).mp hnN
    have hw1 : e * (p : G) * e⁻¹ ∈ P1 := ⟨p, hpP0, rfl⟩
    have hzK : e * y * e⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp heK y).mp hyK
    refine (hmemY ⟨_, hzK⟩).mpr ?_
    have hz : (⟨e * y * e⁻¹, hzK⟩ : K) =
        ⟨_, hNK hx1⟩ * ⟨e * (p : G) * e⁻¹, hP1K hw1⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hz, map_mul, (hN _).mpr hx1, one_mul, hU01]
    exact (mem_img φ).mpr ⟨⟨_, hP1K hw1⟩, hw1, rfl⟩
  have hY3 : ¬ 3 ∣ Nat.card Y := by
    rw [hYcard]
    intro h3d
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3d with h | h
    · exact hN3 h
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h)
      omega
  obtain ⟨S, hS, hES⟩ := CFSG.RankThree.PartTwo.Sec10.exists_isSylowOf_le_normalizer
    (p := 3) (q := 2) hE3 hY3 hEY
  have hSY : S ≤ Y := hS.le
  have hSK : S ≤ K := hSY.trans hYK
  have hS2 : IsPGroup 2 S := hS.isPGroup
  have hScard : Nat.card S = 2 ^ m := by rw [hS.card_eq, hY2]
  have hSφ : ∀ x : K, (x : G) ∈ S → φ x ∈ U0 := fun x hx => (hmemY x).mp (hSY hx)
  have hSsq : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x ∧ x ^ 2 = 1 := by
    intro x hx y hy
    have hxK : x ∈ K := hSK hx
    have hyK : y ∈ K := hSK hy
    obtain ⟨hc, hs⟩ := hElem U0 hU0card _ (hSφ ⟨x, hxK⟩ hx) _ (hSφ ⟨y, hyK⟩ hy)
    refine ⟨?_, ?_⟩
    · have := inj_on_two_group φ hN hNodd hS2 (x := ⟨x, hxK⟩ * ⟨y, hyK⟩)
        (y := ⟨y, hyK⟩ * ⟨x, hxK⟩) (S.mul_mem hx hy) (S.mul_mem hy hx)
        (by rw [map_mul, map_mul]; exact hc)
      exact congrArg Subtype.val this
    · have := inj_on_two_group φ hN hNodd hS2 (x := (⟨x, hxK⟩ : K) ^ 2) (y := 1)
        (S.pow_mem hx 2) S.one_mem (by rw [map_pow, hs, map_one])
      simpa using congrArg Subtype.val this
  have hSelem : CFSG.Assembly.IsElemAbelian 2 S :=
    ⟨⟨⟨fun a b => Subtype.ext (hSsq a a.2 b b.2).1⟩⟩, fun x hx => (hSsq x hx x hx).2⟩
  have htrans : ∀ u ∈ S, u ≠ 1 → ∀ v ∈ S, v ≠ 1 →
      ∃ n ∈ Subgroup.normalizer (S : Set G), n * u * n⁻¹ = v := by
    intro u hu hu1 v hv hv1
    have huK := hSK hu
    have hvK := hSK hv
    have hφne : ∀ w : K, (w : G) ∈ S → (w : G) ≠ 1 → φ w ≠ 1 := by
      intro w hw hw1 h
      have := inj_on_two_group φ hN hNodd hS2 (x := w) (y := 1) hw S.one_mem (by rw [h, map_one])
      exact hw1 (congrArg Subtype.val this)
    obtain ⟨nb, hnb, hnbuv⟩ := hTrans U0 hU0card _ (hSφ ⟨u, huK⟩ hu) (hφne ⟨u, huK⟩ hu hu1) _
      (hSφ ⟨v, hvK⟩ hv) (hφne ⟨v, hvK⟩ hv hv1)
    obtain ⟨ν, hν⟩ := hφ nb
    have hνY : (ν : G) ∈ Subgroup.normalizer (Y : Set G) := by
      apply Subgroup.mem_normalizer_fintype
      intro y hy
      have hyK : y ∈ K := hYK hy
      have hφy : φ ⟨y, hyK⟩ ∈ U0 := (hmemY ⟨y, hyK⟩).mp hy
      have hz : (ν : G) * y * (ν : G)⁻¹ ∈ K := K.mul_mem (K.mul_mem ν.2 hyK) (K.inv_mem ν.2)
      refine (hmemY ⟨_, hz⟩).mpr ?_
      have e : (⟨(ν : G) * y * (ν : G)⁻¹, hz⟩ : K) = ν * ⟨y, hyK⟩ * ν⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hν]
      exact (Subgroup.mem_normalizer_iff.mp hnb _).mp hφy
    set S1 : Subgroup G := S.map (MulAut.conj (ν : G)).toMonoidHom with hS1
    have hS1Y : S1 ≤ Y := by
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hνY x).mp (hSY hx)
    have hS1card : Nat.card S1 = 2 ^ (Nat.card Y).factorization 2 := by
      rw [hS1, Subgroup.card_map_of_injective (MulAut.conj (ν : G)).injective, hScard, hY2]
    have hS1syl : IsSylowOf 2 S1 Y := isSylowOf_of_card hS1Y hS1card
    obtain ⟨k, hkY, hk⟩ := hS1syl.exists_mem_conj hS
    have hkK : k ∈ K := hYK hkY
    refine ⟨k * ν, ?_, ?_⟩
    · apply Subgroup.mem_normalizer_fintype
      intro x hx
      refine (hk _).mpr ?_
      have : k⁻¹ * (k * (ν : G) * x * (k * (ν : G))⁻¹) * k = (ν : G) * x * (ν : G)⁻¹ := by group
      rw [this]
      exact ⟨x, hx, rfl⟩
    · have hφk : φ ⟨k, hkK⟩ ∈ U0 := (hmemY ⟨k, hkK⟩).mp hkY
      have hcomm := (hElem U0 hU0card _ hφk _ (hSφ ⟨v, hvK⟩ hv)).1
      have hmem : (k * (ν : G) * u * (k * (ν : G))⁻¹) ∈ S := by
        have hn : k * (ν : G) ∈ Subgroup.normalizer (S : Set G) := by
          apply Subgroup.mem_normalizer_fintype
          intro x hx
          refine (hk _).mpr ?_
          have : k⁻¹ * (k * (ν : G) * x * (k * (ν : G))⁻¹) * k = (ν : G) * x * (ν : G)⁻¹ := by
            group
          rw [this]
          exact ⟨x, hx, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hn u).mp hu
      have hnK : k * (ν : G) * u * (k * (ν : G))⁻¹ ∈ K :=
        K.mul_mem (K.mul_mem (K.mul_mem hkK ν.2) huK) (K.inv_mem (K.mul_mem hkK ν.2))
      have hKe : (⟨k * (ν : G) * u * (k * (ν : G))⁻¹, hnK⟩ : K) =
          ⟨k, hkK⟩ * ν * ⟨u, huK⟩ * (⟨k, hkK⟩ * ν)⁻¹ := rfl
      have hφeq : φ (⟨k * (ν : G) * u * (k * (ν : G))⁻¹, hnK⟩ : K) = φ ⟨v, hvK⟩ := by
        rw [hKe, map_mul, map_mul, map_mul, map_inv, map_mul, hν]
        calc φ ⟨k, hkK⟩ * nb * φ ⟨u, huK⟩ * (φ ⟨k, hkK⟩ * nb)⁻¹
            = φ ⟨k, hkK⟩ * (nb * φ ⟨u, huK⟩ * nb⁻¹) * (φ ⟨k, hkK⟩)⁻¹ := by group
          _ = φ ⟨k, hkK⟩ * φ ⟨v, hvK⟩ * (φ ⟨k, hkK⟩)⁻¹ := by rw [hnbuv]
          _ = φ ⟨v, hvK⟩ := by rw [hcomm]; group
      have := inj_on_two_group φ hN hNodd hS2 (x := ⟨k * (ν : G) * u * (k * (ν : G))⁻¹, hnK⟩)
        (y := ⟨v, hvK⟩) hmem hv hφeq
      exact congrArg Subtype.val this
  exact ⟨S, hSK, hScard, hSelem, hES, htrans⟩

end Lift

end CFSG.RankThree.PartTwo.Sec8.HeringU3n
