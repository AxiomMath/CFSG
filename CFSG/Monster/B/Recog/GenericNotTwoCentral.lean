module

public import CFSG.Monster.B.Recog.GenericTransferExtremal

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Recog

namespace NotTwoCentral

variable {G : Type*} [Group G]

theorem inv_conj_mem_of_mem_normalizer {X : Subgroup G} {x y : G}
    (hx : x ∈ Subgroup.normalizer (X : Set G)) (hy : y ∈ X) : x⁻¹ * y * x ∈ X :=
  (Subgroup.mem_normalizer_iff.1 hx (x⁻¹ * y * x)).2 (by
    rwa [show x * (x⁻¹ * y * x) * x⁻¹ = y by group])

theorem conj_mem_center_of_mem_normalizer {X : Subgroup G} {x z : G}
    (hx : x ∈ Subgroup.normalizer (X : Set G)) (hzX : z ∈ X) (hz : ∀ y ∈ X, z * y = y * z) :
    x * z * x⁻¹ ∈ X ∧ ∀ y ∈ X, x * z * x⁻¹ * y = y * (x * z * x⁻¹) := by
  refine ⟨(Subgroup.mem_normalizer_iff.1 hx z).1 hzX, fun y hy => ?_⟩
  have hy' := hz _ (inv_conj_mem_of_mem_normalizer hx hy)
  calc x * z * x⁻¹ * y = x * (z * (x⁻¹ * y * x)) * x⁻¹ := by group
    _ = x * ((x⁻¹ * y * x) * z) * x⁻¹ := by rw [hy']
    _ = y * (x * z * x⁻¹) := by group

theorem conj_mem_center_inf_commutator {X : Subgroup G} {x u : G}
    (hx : x ∈ Subgroup.normalizer (X : Set G))
    (hu : u ∈ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆) :
    x * u * x⁻¹ ∈ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆ := by
  obtain ⟨⟨⟨w, hwX⟩, hw, rfl⟩, hu'⟩ := hu
  have hwc : ∀ y ∈ X, w * y = y * w := fun y hy =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hw ⟨y, hy⟩).symm
  obtain ⟨hcX, hcc⟩ := conj_mem_center_of_mem_normalizer hx hwX hwc
  refine ⟨⟨⟨_, hcX⟩, Subgroup.mem_center_iff.2 fun y => Subtype.ext (hcc y y.2).symm, rfl⟩, ?_⟩
  have hXmap : X.map (MulAut.conj x).toMonoidHom ≤ X := by
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hx y).1 hy
  have hmem : (MulAut.conj x).toMonoidHom w ∈ ⁅X, X⁆.map (MulAut.conj x).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hu'
  rw [Subgroup.map_commutator] at hmem
  exact Subgroup.commutator_mono hXmap hXmap hmem

theorem exists_mem_normalizer_of_even [Finite G] {X L : Subgroup G} (hX2 : IsPGroup 2 X)
    (hXL : X ≤ L) (heven : Even (X.relIndex L)) :
    ∃ x : G, x ∈ L ∧ x ∈ Subgroup.normalizer (X : Set G) ∧ x ∉ X ∧
      ∃ Y : Subgroup G, Y ≤ L ∧ Nat.card Y = 2 * Nat.card X ∧
        ∀ y ∈ Y, y ∈ X ∨ x⁻¹ * y ∈ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hX2.exists_card_eq
  have hXcard : Nat.card (X.subgroupOf L) = 2 ^ n :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL).toEquiv).trans hn
  have hdvd : 2 ^ (n + 1) ∣ Nat.card L := by
    have h := Subgroup.relIndex_mul_card X L
    rw [inf_eq_left.2 hXL, hn] at h
    obtain ⟨m, hm⟩ := heven
    rw [← h, hm, pow_succ]
    exact ⟨m, by ring⟩
  obtain ⟨Y, hY, hXY⟩ := Sylow.exists_subgroup_card_pow_succ hdvd hXcard
  have hidx : ((X.subgroupOf L).subgroupOf Y).index = 2 := by
    have h := Subgroup.card_mul_index ((X.subgroupOf L).subgroupOf Y)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXY).toEquiv, hXcard, hY, pow_succ] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos n) h
  have hlt : X.subgroupOf L < Y := lt_of_le_of_ne hXY fun h => by
    have h' := congrArg (fun H : Subgroup L => Nat.card H) h
    simp only [hXcard, hY, pow_succ] at h'
    have := Nat.two_pow_pos n
    omega
  obtain ⟨y, hyY, hyX⟩ := IsConcreteLE.exists_of_lt hlt
  have hN := Subgroup.normal_of_index_eq_two hidx
  refine ⟨y, y.2, ?_, fun h => hyX (Subgroup.mem_subgroupOf.2 h), Y.map L.subtype,
    fun _ ⟨w, _, hw⟩ => hw ▸ w.2, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hhL : h ∈ L := hXL hh
      have hmem : (⟨⟨h, hhL⟩, hXY (Subgroup.mem_subgroupOf.2 hh)⟩ : Y) ∈
          (X.subgroupOf L).subgroupOf Y := Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 hh)
      have hc := hN.conj_mem _ hmem ⟨y, hyY⟩
      exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hc)
    · intro hh
      have hhL : (y : G) * h * (y : G)⁻¹ ∈ L := hXL hh
      have hmem : (⟨⟨_, hhL⟩, hXY (Subgroup.mem_subgroupOf.2 hh)⟩ : Y) ∈
          (X.subgroupOf L).subgroupOf Y := Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 hh)
      have hc := hN.conj_mem _ hmem ⟨y, hyY⟩⁻¹
      have hc' := Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hc)
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv,
        show ∀ a b : G, a⁻¹ * (a * b * a⁻¹) * a = b from fun a b => by group] using hc'
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hY, hn, pow_succ, mul_comm]
  · rintro _ ⟨w, hw, rfl⟩
    by_cases hwX : w ∈ X.subgroupOf L
    · exact Or.inl (Subgroup.mem_subgroupOf.1 hwX)
    · right
      have h := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨y, hyY⟩⁻¹) (b := ⟨w, hw⟩)
      have hyX' : (⟨y, hyY⟩⁻¹ : Y) ∉ (X.subgroupOf L).subgroupOf Y := fun h' => by
        have h'' := ((X.subgroupOf L).subgroupOf Y).inv_mem h'
        rw [inv_inv] at h''
        exact hyX (Subgroup.mem_subgroupOf.1 h'')
      have hwX' : (⟨w, hw⟩ : Y) ∉ (X.subgroupOf L).subgroupOf Y := fun h' =>
        hwX (Subgroup.mem_subgroupOf.1 h')
      have hm := h.2 (iff_of_false hyX' hwX')
      have hm' := Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hm)
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype] using hm'

theorem odd_relIndex_centralizer_of_extremal [Finite G] {d β : G} {X U : Subgroup G}
    (hX2 : IsPGroup 2 X) (hdX : d ∈ X) (hXd : X ≤ Subgroup.centralizer {d})
    (hXβ : X ≤ Subgroup.centralizer {β})
    (hXsyl : Odd (X.relIndex (Subgroup.centralizer {d} ⊓ Subgroup.centralizer {β})))
    (hUinv : ∀ x ∈ Subgroup.normalizer (X : Set G), ∀ u ∈ U, x * u * x⁻¹ ∈ U)
    (hZ : ∀ z ∈ X, (∀ y ∈ X, z * y = y * z) →
      z ∈ U ∨ d⁻¹ * z ∈ U ∨ β⁻¹ * z ∈ U ∨ (d * β)⁻¹ * z ∈ U)
    (hdU : d ∉ U) (hβdU : β⁻¹ * d ∉ U)
    (hc : ∀ u ∈ U, IsConj d (d * u) → u = 1)
    (hd : ∀ u ∈ U, ∃ u' ∈ U, u' ≠ u ∧ IsConj (d * β * u) (d * β * u')) :
    Odd (X.relIndex (Subgroup.centralizer {β})) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨x, hxβ, hxN, hxX, Y, hYL, hYcard, hYX⟩ := exists_mem_normalizer_of_even hX2 hXβ hodd
  have hxinv : x⁻¹ ∈ Subgroup.normalizer (X : Set G) := Subgroup.inv_mem _ hxN
  have hxβ' : x * β = β * x := Subgroup.mem_centralizer_singleton_iff.1 hxβ
  have hxd : x ∉ Subgroup.centralizer {d} := by
    intro hxd
    have hYle : Y ≤ Subgroup.centralizer {d} ⊓ Subgroup.centralizer {β} := by
      intro y hy
      refine ⟨?_, hYL hy⟩
      rcases hYX y hy with h | h
      · exact hXd h
      · have := (Subgroup.centralizer {d}).mul_mem hxd (hXd h)
        rwa [mul_inv_cancel_left] at this
    have h1 := Subgroup.card_dvd_of_le hYle
    have h2 := Subgroup.relIndex_mul_card X (Subgroup.centralizer {d} ⊓ Subgroup.centralizer {β})
    rw [inf_eq_left.2 (le_inf hXd hXβ)] at h2
    rw [hYcard, ← h2] at h1
    have h3 := Nat.dvd_of_mul_dvd_mul_right Nat.card_pos h1
    exact (Nat.not_even_iff_odd.2 hXsyl) (even_iff_two_dvd.2 h3)
  have hdc : ∀ y ∈ X, d * y = y * d := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hXd hy)).symm
  obtain ⟨hzX, hzc⟩ := conj_mem_center_of_mem_normalizer hxN hdX hdc
  have hdz : IsConj d (x * d * x⁻¹) := isConj_iff.2 ⟨x, rfl⟩
  have hback : ∀ v : G, x⁻¹ * (x * d * x⁻¹ * v) * x = d * (x⁻¹ * v * x) := fun v => by group
  rcases hZ _ hzX hzc with h | h | h | h
  · have := hUinv _ hxinv _ h
    rw [inv_inv, show x⁻¹ * (x * d * x⁻¹) * x = d by group] at this
    exact hdU this
  · have h1 := hc _ h (by rwa [mul_inv_cancel_left])
    rw [inv_mul_eq_one] at h1
    exact hxd (Subgroup.mem_centralizer_singleton_iff.2 (by
      calc x * d = x * d * x⁻¹ * x := by group
        _ = d * x := by rw [← h1]))
  · have := hUinv _ hxinv _ h
    have h0 : x⁻¹ * β * x = β := by rw [mul_assoc, ← hxβ', inv_mul_cancel_left]
    have hβx : x⁻¹ * β⁻¹ * x = β⁻¹ := by
      calc x⁻¹ * β⁻¹ * x = (x⁻¹ * β * x)⁻¹ := by group
        _ = β⁻¹ := by rw [h0]
    rw [inv_inv, show x⁻¹ * (β⁻¹ * (x * d * x⁻¹)) * x = (x⁻¹ * β⁻¹ * x) * d by group, hβx]
      at this
    exact hβdU this
  · obtain ⟨u', hu', hne, hconj⟩ := hd _ h
    have hz : d * β * ((d * β)⁻¹ * (x * d * x⁻¹)) = x * d * x⁻¹ := by group
    rw [hz] at hconj
    have hv : ((d * β)⁻¹ * (x * d * x⁻¹))⁻¹ * u' ∈ U := U.mul_mem (U.inv_mem h) hu'
    have hv1 : ((d * β)⁻¹ * (x * d * x⁻¹))⁻¹ * u' ≠ 1 := fun h1 =>
      hne (inv_mul_eq_one.1 h1).symm
    have hu'' := hUinv _ hxinv _ hv
    rw [inv_inv] at hu''
    have hw : IsConj (d * β * u') (d * (x⁻¹ * (((d * β)⁻¹ * (x * d * x⁻¹))⁻¹ * u') * x)) := by
      refine isConj_iff.2 ⟨x⁻¹, ?_⟩
      rw [inv_inv, ← hback]
      group
    have h1 := hc _ hu'' (hdz.trans (hconj.trans hw))
    exact hv1 (by
      have := congrArg (fun v => x * v * x⁻¹) h1
      simpa [mul_assoc] using this)

theorem relIndex_eq_two_of_not_mem {H K T : Subgroup G} (hKH : K.relIndex H = 2) (hTH : T ≤ H)
    {β : G} (hβT : β ∈ T) (hβK : β ∉ K) : K.relIndex T = 2 := by
  have hN := Subgroup.normal_of_index_eq_two (H := K.subgroupOf H) hKH
  have hdvd : (K.subgroupOf H).relIndex (T.subgroupOf H) ∣ 2 := by
    rw [← show (K.subgroupOf H).index = 2 from hKH]
    exact Subgroup.relIndex_dvd_index_of_normal _ _
  rw [Subgroup.relIndex_subgroupOf hTH] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact absurd (Subgroup.relIndex_eq_one.1 h hβT) hβK
  · exact h

end NotTwoCentral

open NotTwoCentral

theorem false_of_sylow_of_extremal {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)
    {d β : G} {K X U : Subgroup G} (hKT : K.relIndex T = 2) (hβ : β ^ 2 = 1)
    (hGβ : ∀ L : Subgroup G, L.index = 2 → β ∈ L)
    (hX2 : IsPGroup 2 X) (hdX : d ∈ X) (hXd : X ≤ Subgroup.centralizer {d})
    (hXβ : X ≤ Subgroup.centralizer {β})
    (hXsyl : Odd (X.relIndex (Subgroup.centralizer {d} ⊓ Subgroup.centralizer {β})))
    (hUinv : ∀ x ∈ Subgroup.normalizer (X : Set G), ∀ u ∈ U, x * u * x⁻¹ ∈ U)
    (hZ : ∀ z ∈ X, (∀ y ∈ X, z * y = y * z) →
      z ∈ U ∨ d⁻¹ * z ∈ U ∨ β⁻¹ * z ∈ U ∨ (d * β)⁻¹ * z ∈ U)
    (hdU : d ∉ U) (hβdU : β⁻¹ * d ∉ U)
    (hc : ∀ u ∈ U, IsConj d (d * u) → u = 1)
    (hd : ∀ u ∈ U, ∃ u' ∈ U, u' ≠ u ∧ IsConj (d * β * u) (d * β * u'))
    (he : ∀ u ∈ K, IsConj β u → 2 * Nat.card X ∣
      Nat.card (Subgroup.centralizer {d} ⊓ Subgroup.centralizer {u} : Subgroup G)) :
    False := by
  have hXC := odd_relIndex_centralizer_of_extremal hX2 hdX hXd hXβ hXsyl hUinv hZ hdU hβdU hc hd
  obtain ⟨g, hgK, -⟩ := exists_conj_mem_odd_relIndex_of_transfer T hKT hβ hGβ
  have h1 := he _ hgK (isConj_iff.2 ⟨g, rfl⟩)
  have h2 := Subgroup.card_dvd_of_le (inf_le_right : Subgroup.centralizer {d} ⊓
    Subgroup.centralizer {g * β * g⁻¹} ≤ Subgroup.centralizer {g * β * g⁻¹})
  have h3 : Nat.card (Subgroup.centralizer {g * β * g⁻¹}) =
      Nat.card (Subgroup.centralizer {β}) := by
    have e := TransferExtremal.centralizer_conj_eq_map β g⁻¹
    rw [inv_inv] at e
    rw [e, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have h4 := Subgroup.relIndex_mul_card X (Subgroup.centralizer {β})
  rw [inf_eq_left.2 hXβ] at h4
  rw [h3, ← h4] at h2
  have h5 := Nat.dvd_of_mul_dvd_mul_right Nat.card_pos (h1.trans h2)
  exact (Nat.not_even_iff_odd.2 hXC) (even_iff_two_dvd.2 h5)

theorem two_dvd_index_of_extremal {G : Type*} [Group G] [Finite G] (T : Subgroup G)
    (hT2 : IsPGroup 2 T) {d β : G} {K X U : Subgroup G} (hKT : K.relIndex T = 2)
    (hβ : β ^ 2 = 1) (hGβ : ∀ L : Subgroup G, L.index = 2 → β ∈ L)
    (hX2 : IsPGroup 2 X) (hdX : d ∈ X) (hXd : X ≤ Subgroup.centralizer {d})
    (hXβ : X ≤ Subgroup.centralizer {β})
    (hXsyl : Odd (X.relIndex (Subgroup.centralizer {d} ⊓ Subgroup.centralizer {β})))
    (hUinv : ∀ x ∈ Subgroup.normalizer (X : Set G), ∀ u ∈ U, x * u * x⁻¹ ∈ U)
    (hZ : ∀ z ∈ X, (∀ y ∈ X, z * y = y * z) →
      z ∈ U ∨ d⁻¹ * z ∈ U ∨ β⁻¹ * z ∈ U ∨ (d * β)⁻¹ * z ∈ U)
    (hdU : d ∉ U) (hβdU : β⁻¹ * d ∉ U)
    (hc : ¬ 2 ∣ T.index → ∀ u ∈ U, IsConj d (d * u) → u = 1)
    (hd : ∀ u ∈ U, ∃ u' ∈ U, u' ≠ u ∧ IsConj (d * β * u) (d * β * u'))
    (he : ∀ u ∈ K, IsConj β u → 2 * Nat.card X ∣
      Nat.card (Subgroup.centralizer {d} ⊓ Subgroup.centralizer {u} : Subgroup G)) :
    2 ∣ T.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hT
  exact false_of_sylow_of_extremal (hT2.toSylow hT) hKT hβ hGβ hX2 hdX hXd hXβ hXsyl hUinv hZ
    hdU hβdU (hc hT) hd he

theorem two_dvd_index_centralizer_of_extremal {G : Type*} [Group G] [Finite G] (T : Subgroup G)
    (hT2 : IsPGroup 2 T) {d β : G} (hTd : T ≤ Subgroup.centralizer {d})
    (hTodd : Odd (T.relIndex (Subgroup.centralizer {d}))) {K X U : Subgroup G}
    (hKT : K.relIndex T = 2) (hβ : β ^ 2 = 1) (hGβ : ∀ L : Subgroup G, L.index = 2 → β ∈ L)
    (hX2 : IsPGroup 2 X) (hdX : d ∈ X) (hXd : X ≤ Subgroup.centralizer {d})
    (hXβ : X ≤ Subgroup.centralizer {β})
    (hXsyl : Odd (X.relIndex (Subgroup.centralizer {d} ⊓ Subgroup.centralizer {β})))
    (hUinv : ∀ x ∈ Subgroup.normalizer (X : Set G), ∀ u ∈ U, x * u * x⁻¹ ∈ U)
    (hZ : ∀ z ∈ X, (∀ y ∈ X, z * y = y * z) →
      z ∈ U ∨ d⁻¹ * z ∈ U ∨ β⁻¹ * z ∈ U ∨ (d * β)⁻¹ * z ∈ U)
    (hdU : d ∉ U) (hβdU : β⁻¹ * d ∉ U)
    (hc : ¬ 2 ∣ T.index → ∀ u ∈ U, IsConj d (d * u) → u = 1)
    (hd : ∀ u ∈ U, ∃ u' ∈ U, u' ≠ u ∧ IsConj (d * β * u) (d * β * u'))
    (he : ∀ u ∈ K, IsConj β u → 2 * Nat.card X ∣
      Nat.card (Subgroup.centralizer {d} ⊓ Subgroup.centralizer {u} : Subgroup G)) :
    2 ∣ (Subgroup.centralizer {d}).index := by
  have h := two_dvd_index_of_extremal T hT2 hKT hβ hGβ hX2 hdX hXd hXβ hXsyl hUinv hZ hdU hβdU
    hc hd he
  rw [← Subgroup.relIndex_mul_index hTd] at h
  exact (Nat.Prime.dvd_mul Nat.prime_two).1 h |>.resolve_left
    (fun h2 => (Nat.not_even_iff_odd.2 hTodd) (even_iff_two_dvd.2 h2))

end CFSG.Monster.B.Recog
