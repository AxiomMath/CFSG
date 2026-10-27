module

public import CFSG.Walter.Ree.Thompson1.Hyp
public import CFSG.Walter.ReeOrder.WardLocal.Two

public section

namespace CFSG.Walter.Ree

open CFSG.Walter.Ward

section Transport

variable {M : Type*} [Group M]

theorem map_subtype_center (X : Subgroup M) :
    (Subgroup.center X).map X.subtype = X ⊓ Subgroup.centralizer (X : Set M) := by
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.mem_center_iff, Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, fun x hx => congrArg Subtype.val (hy ⟨x, hx⟩)⟩
  · rintro ⟨hzX, hzc⟩
    exact ⟨⟨z, hzX⟩, fun y => Subtype.ext (hzc y y.2), rfl⟩

variable {N : Subgroup M}

theorem map_subtype_centralizer (S : Set N) :
    (Subgroup.centralizer S).map N.subtype = N ⊓ Subgroup.centralizer (N.subtype '' S) := by
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.coe_subtype, Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val (hy x hx)
  · rintro ⟨hzN, hzc⟩
    exact ⟨⟨z, hzN⟩, fun x hx => Subtype.ext (hzc x ⟨x, hx, rfl⟩), rfl⟩

theorem map_subtype_inj {X Y : Subgroup N} : X = Y ↔ X.map N.subtype = Y.map N.subtype :=
  ⟨fun h => h ▸ rfl, fun h => Subgroup.map_injective N.subtype_injective h⟩

theorem map_subtype_top : (⊤ : Subgroup N).map N.subtype = N := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem card_map_subtype (X : Subgroup N) : Nat.card (X.map N.subtype) = Nat.card X :=
  Subgroup.card_map_of_injective N.subtype_injective

theorem isElementaryAbelian_of_map {M' : Type*} [Group M'] {f : M →* M'}
    (hf : Function.Injective f) {X : Subgroup M} {p : ℕ}
    (h : IsElementaryAbelian p (X.map f)) : IsElementaryAbelian p X := by
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · have hab := h.toIsMulCommutative.is_comm.comm (⟨f a, a, a.2, rfl⟩ : X.map f)
      ⟨f b, b, b.2, rfl⟩
    have := congrArg Subtype.val hab
    simp only [Subgroup.coe_mul] at this
    rw [← map_mul, ← map_mul] at this
    exact Subtype.ext (hf this)
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => ?_
    have ha := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h.exponent_dvd_p
      (⟨f a, a, a.2, rfl⟩ : X.map f)
    have := congrArg Subtype.val ha
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [← map_pow] at this
    exact Subtype.ext (hf (this.trans (map_one f).symm))

end Transport

variable {G : Type} [Group G] [Finite G]

theorem ward_thompsonIHyp
    (h : ReeTypeHyp G) (P : Sylow 3 G) :
    ThompsonIHyp (Subgroup.normalizer ((P : Subgroup G) : Set G)) h.q := by
  obtain ⟨hcard, -, hZel, hZcard, -, hP1c, -, -, hP1Ω, hP1P, -, hP1el, hP1card, -, hf, hh, -,
    W, hWcyc, hWcard, hPW, hNPW, hJ, hR⟩ := WardLocal.ward_two h P
  set Pg : Subgroup G := (P : Subgroup G) with hPgdef
  set N : Subgroup G := Subgroup.normalizer (Pg : Set G) with hN
  set Z : Subgroup G := (Subgroup.center Pg).map Pg.subtype with hZ
  set P₁ : Subgroup G := (commutator Pg).map Pg.subtype with hP₁
  have hPgN : Pg ≤ N := Subgroup.le_normalizer
  have hWN : W ≤ N := by rw [hNPW]; exact le_sup_right
  set 𝔓 : Subgroup N := Pg.subgroupOf N with h𝔓
  set ℜ : Subgroup N := W.subgroupOf N with hℜ
  have m𝔓 : 𝔓.map N.subtype = Pg := Subgroup.map_subgroupOf_eq_of_le hPgN
  have mℜ : ℜ.map N.subtype = W := Subgroup.map_subgroupOf_eq_of_le hWN
  have mcomm : (⁅𝔓, 𝔓⁆ : Subgroup N).map N.subtype = P₁ := by
    rw [Subgroup.map_commutator, m𝔓, hP1c]
  have mZ : ((Subgroup.center 𝔓).map 𝔓.subtype).map N.subtype = Z := by
    rw [map_subtype_center, Subgroup.map_inf_eq _ _ N.subtype N.subtype_injective, m𝔓,
      map_subtype_centralizer, hZ, map_subtype_center]
    have : N.subtype '' (𝔓 : Set N) = (Pg : Set G) := by
      rw [← Subgroup.coe_map, m𝔓]
    rw [this, ← inf_assoc, inf_eq_left.mpr hPgN]
  have mcen : ∀ x : N, (𝔓 ⊓ Subgroup.centralizer ({x} : Set N)).map N.subtype =
      Pg ⊓ Subgroup.centralizer ({(x : G)} : Set G) := by
    intro x
    rw [Subgroup.map_inf_eq _ _ N.subtype N.subtype_injective, m𝔓, map_subtype_centralizer,
      Set.image_singleton, ← inf_assoc, inf_eq_left.mpr hPgN]
    rfl
  have hJmem : ∀ x : N, x ∈ ⁅𝔓, 𝔓⁆ ↔ (x : G) ∈ P₁ := fun x => by
    rw [← mcomm]
    exact (Subgroup.mem_map_iff_mem N.subtype_injective).symm
  have hZmem : ∀ x : N, x ∈ (Subgroup.center 𝔓).map 𝔓.subtype ↔ (x : G) ∈ Z := fun x => by
    rw [← mZ]
    exact (Subgroup.mem_map_iff_mem N.subtype_injective).symm
  have h𝔓mem : ∀ x : N, x ∈ 𝔓 ↔ (x : G) ∈ Pg := fun x => Subgroup.mem_subgroupOf
  have hℜmem : ∀ x : N, x ∈ ℜ ↔ (x : G) ∈ W := fun x => Subgroup.mem_subgroupOf
  have hℜcard : Nat.card ℜ = h.q - 1 := by rw [← card_map_subtype, mℜ, hWcard]
  have hℜcyc : IsCyclic ℜ := by
    have e : ℜ ≃* W := (Subgroup.equivMapOfInjective ℜ N.subtype N.subtype_injective).trans
      (MulEquiv.subgroupCongr mℜ)
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  refine ⟨?_, 𝔓, ℜ, ?_⟩
  ·
    have hnorm : 𝔓.Normal := Subgroup.normal_in_normalizer
    have hsup : 𝔓 ⊔ ℜ = ⊤ := by
      rw [map_subtype_inj, Subgroup.map_sup, m𝔓, mℜ, ← hNPW, map_subtype_top]
    have hinf : 𝔓 ⊓ ℜ = ⊥ := by
      rw [map_subtype_inj, Subgroup.map_inf_eq _ _ N.subtype N.subtype_injective, m𝔓, mℜ, hPW,
        Subgroup.map_bot]
    have h1 := Subgroup.relIndex_mul_card (H := 𝔓) (K := 𝔓 ⊔ ℜ)
    rw [Subgroup.relIndex_sup_left, inf_eq_left.mpr le_sup_left] at h1
    have h2 := Subgroup.relIndex_mul_card (H := 𝔓) (K := ℜ)
    rw [hinf, Subgroup.card_bot] at h2
    rw [hsup, Subgroup.card_top] at h1
    rw [← h1, ← card_map_subtype 𝔓, m𝔓, hcard, ← hℜcard]
    have h3 : 𝔓.relIndex ℜ = Nat.card ℜ := by rw [← h2, mul_one]
    rw [h3, mul_comm]
  refine
    { sup_eq_top := ?_, normal := Subgroup.normal_in_normalizer, card_P := ?_, card_R := hℜcard,
      isCyclic_R := hℜcyc, centralizer_eq_bot := ?_, card_commutator := ?_,
      elementary_commutator := ?_, commutator_commutator := ?_, card_center := ?_,
      elementary_center := ?_, commutator_eq_prod := ?_, centralizer_of_mem_commutator := ?_,
      commutator_eq_omega := ?_, centralizer_of_notMem_commutator := ?_ }
  · rw [map_subtype_inj, Subgroup.map_sup, m𝔓, mℜ, ← hNPW, map_subtype_top]
  · rw [← card_map_subtype, m𝔓, hcard]
  ·
    intro r hr hr2
    rw [map_subtype_inj, mcen, Subgroup.map_bot, eq_bot_iff]
    obtain ⟨w, hw⟩ := hWcyc.exists_generator
    have hwo : orderOf (w : G) = h.q - 1 := by
      rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hw, hWcard]
    have hq1 : 2 ∣ h.q - 1 := by
      have := hJ
      have hodd : Odd h.q := by
        rw [ReeTypeHyp.q]
        exact Odd.pow (Nat.Prime.odd_of_ne_two Fact.out h.p_ne_two)
      exact (Nat.Odd.sub_odd hodd odd_one).two_dvd
    have hRo : orderOf ((w : G) ^ 2) = (h.q - 1) / 2 := by
      rw [orderOf_pow' _ two_ne_zero, hwo, Nat.gcd_eq_right hq1]
    obtain ⟨k, hk⟩ := hw ⟨(r : G), (hℜmem r).mp hr⟩
    have hk' : (w : G) ^ k = (r : G) := by
      have := congrArg Subtype.val hk
      simpa using this
    have hr2mem : (r : G) ^ 2 ∈ Subgroup.zpowers ((w : G) ^ 2) := by
      refine ⟨k, ?_⟩
      show ((w : G) ^ 2) ^ k = (r : G) ^ 2
      rw [← hk', ← zpow_natCast (w : G) 2, ← zpow_mul, ← zpow_natCast ((w : G) ^ k) 2,
        ← zpow_mul, mul_comm]
    have hr21 : (r : G) ^ 2 ≠ 1 := by
      intro h1
      exact hr2 (Subtype.ext (by simpa using h1))
    have hbot := hR _ (W.pow_mem w.2 2) hRo _ hr2mem hr21
    intro x hx
    rw [← hbot]
    obtain ⟨hxP, hxc⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hxP, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxc ⊢
    have hc : Commute x (r : G) := hxc
    exact (hc.pow_right 2).eq
  · rw [← card_map_subtype, mcomm, hP1card]
  · exact isElementaryAbelian_of_map N.subtype_injective (mcomm ▸ hP1el)
  · rw [map_subtype_inj, Subgroup.map_commutator, mcomm, m𝔓, mZ, hP1P]
  · rw [← Subgroup.card_map_of_injective 𝔓.subtype_injective, ← card_map_subtype, mZ, hZcard]
  · have h1 : IsElementaryAbelian 3 (((Subgroup.center 𝔓).map 𝔓.subtype).map N.subtype) :=
      mZ ▸ hZel
    exact isElementaryAbelian_of_map 𝔓.subtype_injective
      (isElementaryAbelian_of_map N.subtype_injective h1)
  ·
    intro t ht ht2
    have htW : (t : G) ∈ W := (hℜmem t).mp ht
    have ht2' : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe, ht2]
    obtain ⟨-, -, -, hZt, hP1eq⟩ := hJ _ htW ht2'
    constructor
    · rw [map_subtype_inj, Subgroup.map_sup, mcomm, mcen, mZ, hP1eq, sup_comm]
    · rw [map_subtype_inj, Subgroup.map_inf_eq _ _ N.subtype N.subtype_injective, mcen, mZ,
        Subgroup.map_bot, eq_bot_iff, ← hZt]
      intro x hx
      exact ⟨hx.2, hx.1.2⟩
  ·
    intro x hx hxZ
    rw [map_subtype_inj, mcen, mcomm]
    exact hf _ ((hJmem x).mp hx) (fun h' => hxZ ((hZmem x).mpr h'))
  ·
    rw [map_subtype_inj, mcomm, MonoidHom.map_closure, hP1Ω]
    congr 1
    ext y
    constructor
    · rintro ⟨hy, hy3⟩
      exact ⟨⟨y, hPgN hy⟩, ⟨(h𝔓mem _).mpr hy, Subtype.ext (by simpa using hy3)⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hx3⟩, rfl⟩
      exact ⟨(h𝔓mem x).mp hx, by simpa using congrArg Subtype.val hx3⟩
  ·
    intro x hx hxc
    rw [map_subtype_inj, mcen, Subgroup.map_sup, mZ, MonoidHom.map_zpowers]
    exact (hh _ ((h𝔓mem x).mp hx) (fun h' => hxc ((hJmem x).mpr h'))).2.2

end CFSG.Walter.Ree
