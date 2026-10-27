module

public import CFSG.Quasithin.EmptyFaithful.S152Defs
public import CFSG.Quasithin.EmptyFaithful.S152N2Shapes
public import CFSG.Quasithin.EmptyFaithful.S152N2Z15

public section

namespace CFSG.Quasithin

namespace S152N2

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Omega4PlusIsS3xS3 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (X : Subgroup (MulAut V)), IsOmegaFourPlus X →
    Nonempty (↥X ≃* DihedralGroup 3 × DihedralGroup 3)

@[expose] def Frobenius20IsSz2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X = 20 →
    (∃ N : Subgroup X, N.Normal ∧ Nat.card N = 5 ∧
      ∀ x : X, (∀ n ∈ N, x * n = n * x) → x ∈ N) →
    Nonempty (X ≃* ↥(CFSG.Open.Sz 0))

private def d3Fun : DihedralGroup 3 → Equiv.Perm (Fin 3)
  | DihedralGroup.r i => Equiv.subRight (i : Fin 3)
  | DihedralGroup.sr i => Equiv.subLeft (i : Fin 3)

private def d3Hom : DihedralGroup 3 →* Equiv.Perm (Fin 3) where
  toFun := d3Fun
  map_one' := by decide
  map_mul' := by decide

theorem nonempty_d3_equiv_perm : Nonempty (DihedralGroup 3 ≃* Equiv.Perm (Fin 3)) :=
  ⟨MulEquiv.ofBijective d3Hom (by constructor <;> decide)⟩

variable {Γ : Type*} [Group Γ]

theorem sq_eq_one_of_mem_card_two {B : Subgroup Γ} (hBc : Nat.card B = 2) {b : Γ} (hbB : b ∈ B) :
    b ^ 2 = 1 := by
  have hpow : (⟨b, hbB⟩ : B) ^ (Nat.card B) = 1 := pow_card_eq_one'
  rw [hBc] at hpow
  exact congrArg Subtype.val hpow

theorem case_one [Finite Γ] {X Tb : Subgroup Γ} (hTb : IsSylowTwoOf Tb X)
    (hX : Nonempty (↥X ≃* DihedralGroup 3)) (Bs : Set (Subgroup Γ))
    (hBs : ∀ B ∈ Bs, B ≤ Tb ∧ Nat.card B = 2) :
    IsSmallGroup152 ↥X ∧ ShapeConcl X Tb Bs := by
  obtain ⟨e⟩ := hX
  obtain ⟨e'⟩ := nonempty_d3_equiv_perm
  have hcard : Nat.card X = 2 * 3 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hnc : ∃ a ∈ X, ∃ b ∈ X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ : ∃ a b : DihedralGroup 3, a * b ≠ b * a := by decide
    refine ⟨(e.symm a : Γ), (e.symm a).2, (e.symm b : Γ), (e.symm b).2, fun h => hab ?_⟩
    have h2 : e.symm a * e.symm b = e.symm b * e.symm a := Subtype.ext h
    have h3 := congrArg e h2
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h3
  exact ⟨Or.inl ⟨e.trans e'⟩,
    shapeConcl_of_dihedralLike hTb Nat.prime_three (by norm_num) hcard hnc Bs hBs⟩

theorem case_two_false {X : Subgroup Γ}
    (e : ↥X ≃* DihedralGroup 3 × Multiplicative (ZMod 3)) {B : Subgroup Γ} (hBX : B ≤ X)
    (hstar : ∀ y ∈ X, y ^ 3 = 1 → (∀ b ∈ B, b * y = y * b) → y = 1) : False := by
  set y' : ↥X := e.symm (1, Multiplicative.ofAdd (1 : ZMod 3)) with hy'
  have hy3 : y' ^ 3 = 1 := by
    rw [hy', ← map_pow]
    have : ((1 : DihedralGroup 3), Multiplicative.ofAdd (1 : ZMod 3)) ^ 3 = 1 := by decide
    rw [this]
    exact MulEquiv.map_one _
  have hcentral : ∀ x : ↥X, x * y' = y' * x := by
    intro x
    apply e.injective
    rw [map_mul, map_mul, hy', MulEquiv.apply_symm_apply]
    obtain ⟨a, c⟩ := e x
    simp only [Prod.mk_mul_mk, one_mul, mul_one]
    exact Prod.ext rfl (mul_comm c _)
  have hy1 : y' ≠ 1 := by
    intro h
    have h2 : e y' = e 1 := by rw [h]
    rw [hy', MulEquiv.apply_symm_apply, MulEquiv.map_one] at h2
    have h3 : Multiplicative.ofAdd (1 : ZMod 3) = 1 := congrArg Prod.snd h2
    exact (by decide : (Multiplicative.ofAdd (1 : ZMod 3) : Multiplicative (ZMod 3)) ≠ 1) h3
  have := hstar (y' : Γ) y'.2 (by rw [← Subgroup.coe_pow, hy3]; rfl) (fun b hb => by
    have := congrArg Subtype.val (hcentral ⟨b, hBX hb⟩)
    exact this)
  exact hy1 (Subtype.ext this)

theorem case_five_small {V : Type} [CommGroup V] [Finite V] (hFr : Frobenius20IsSz2)
    (hV2 : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    {X X₀ Tb : Subgroup (MulAut V)} (hTb : IsSylowTwoOf Tb X) (hX₀X : X₀ ≤ X)
    (hXn : X ≤ Subgroup.normalizer (X₀ : Set (MulAut V)))
    (hD5 : Nonempty (↥X₀ ≃* DihedralGroup 5))
    (hF : ∀ K : Subgroup (MulAut V), K ≤ X → X ≤ Subgroup.normalizer (K : Set (MulAut V)) →
      (∀ a ∈ K, ∀ b ∈ K, a * b = b * a) → K ≤ X₀)
    (Bs : Set (Subgroup (MulAut V))) (hBs : ∀ B ∈ Bs, B ≤ Tb ∧ Nat.card B = 2) :
    IsSmallGroup152 ↥X ∧ ShapeConcl X Tb Bs := by
  have : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V → V)) (fun f g h => DFunLike.coe_injective h)
  obtain ⟨e⟩ := hD5
  have h10 : Nat.card X₀ = 10 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hnc : ∃ a ∈ X₀, ∃ b ∈ X₀, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ : ∃ a b : DihedralGroup 5, a * b ≠ b * a := by decide
    refine ⟨(e.symm a : MulAut V), (e.symm a).2, (e.symm b : MulAut V), (e.symm b).2,
      fun h => hab ?_⟩
    have h2 : e.symm a * e.symm b = e.symm b * e.symm a := Subtype.ext h
    have h3 := congrArg e h2
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h3
  obtain ⟨N, hNX₀, hnorm, hcardN, hC, hdvd⟩ := five_small hV2 hcard hX₀X hXn h10 hnc hF
  have hNX : N ≤ X := hNX₀.trans hX₀X
  have h10X : 10 ∣ Nat.card X := by
    have := Subgroup.card_dvd_of_le hX₀X
    rwa [h10] at this
  have hXle : Nat.card X ≤ 20 := Nat.le_of_dvd (by norm_num) hdvd
  have hXpos : 0 < Nat.card X := Nat.card_pos
  have hX1020 : Nat.card X = 10 ∨ Nat.card X = 20 := by omega
  rcases hX1020 with h | h
  · have hXeq : X₀ = X := Subgroup.eq_of_le_of_card_ge hX₀X (by rw [h, h10])
    subst hXeq
    have hcardX : Nat.card X₀ = 2 * 5 := h
    refine ⟨Or.inr (Or.inl ⟨e⟩), ?_⟩
    exact shapeConcl_of_dihedralLike hTb (by norm_num) (by norm_num) hcardX hnc Bs hBs
  · have hidx : (N.subgroupOf X).index = 4 := by
      have h1 := (N.subgroupOf X).card_mul_index
      have h2 : Nat.card (N.subgroupOf X) = 5 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv, hcardN]
      rw [h2, h] at h1
      omega
    have hSC : ∀ x : ↥X, (∀ n ∈ N.subgroupOf X, x * n = n * x) → x ∈ N.subgroupOf X := by
      intro x hx
      apply hC x.1 x.2
      intro n hn
      have := hx ⟨n, hNX hn⟩ hn
      exact congrArg Subtype.val this
    have hsz : Nonempty (↥X ≃* ↥(CFSG.Open.Sz 0)) :=
      hFr ↥X h ⟨N.subgroupOf X, hnorm, by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv, hcardN], hSC⟩
    refine ⟨Or.inr (Or.inr hsz), ?_⟩
    have hpow : ∀ x ∈ X, ∃ k : ℕ, x ^ (2 ^ k) ∈ N := by
      intro x hx
      refine ⟨2, ?_⟩
      have := Subgroup.pow_index_mem (N.subgroupOf X) (⟨x, hx⟩ : ↥X)
      rw [hidx] at this
      exact this
    obtain ⟨hON, hcomm, hinv⟩ := prime_normal_facts (by norm_num : Nat.Prime 5) (by norm_num)
      hNX hnorm hcardN hC hpow
    refine shapeConcl_of_oddCore hTb hON hcomm hC Bs fun B hB => ?_
    obtain ⟨hBT, hBc⟩ := hBs B hB
    refine ⟨hBT, hBc, fun b hbB hb1 n hn => ?_⟩
    have hb2 : b ^ 2 = 1 := sq_eq_one_of_mem_card_two hBc hbB
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hb2)
    have := hinv b (hTb.1 (hBT hbB)) hb2 hb1 n hn
    rw [hbinv] at this ⊢
    exact this

theorem case_five_z15 {V : Type} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1)
    (hcard : Nat.card V = 16) {X F B : Subgroup (MulAut V)} (hFX : F ≤ X)
    (hFn : X ≤ Subgroup.normalizer (F : Set (MulAut V)))
    (hF15 : Nonempty (↥F ≃* Multiplicative (ZMod 15))) (hBX : B ≤ X) (hB2 : Nat.card B = 2)
    (hcomm4 : Nat.card (commV B) = 4)
    (hstar : ∀ y ∈ X, y ^ 3 = 1 → (∀ b ∈ B, b * y = y * b) → y = 1) : False := by
  have : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V → V)) (fun f g h => DFunLike.coe_injective h)
  obtain ⟨e⟩ := hF15
  obtain ⟨b, -, hb2, hBeq⟩ := exists_zpowers_eq_of_card_two hB2
  set z' : ↥F := e.symm (Multiplicative.ofAdd (1 : ZMod 15)) with hz'
  set z : MulAut V := (z' : MulAut V) with hzdef
  have hord' : orderOf z' = 15 := by
    rw [hz', MulEquiv.orderOf_eq, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  have hz : orderOf z = 15 := by rw [hzdef, Subgroup.orderOf_coe]; exact hord'
  have hzF : z ∈ F := z'.2
  have hFeq : F = Subgroup.zpowers z := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · exact (Subgroup.zpowers_le).mpr hzF
    · rw [Nat.card_zpowers, hz, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card,
        Fintype.card_multiplicative, ZMod.card]
  have hbB : b ∈ B := by rw [hBeq]; exact Subgroup.mem_zpowers b
  have hbX : b ∈ X := hBX hbB
  have hbz : b * z * b⁻¹ ∈ Subgroup.zpowers z := by
    rw [← hFeq]
    exact (Subgroup.mem_normalizer_iff.mp (hFn hbX) z).mp hzF
  have hcomm4' : Nat.card (commV (Subgroup.zpowers b)) = 4 := by rw [← hBeq]; exact hcomm4
  have hfixb : Nat.card (fixV (Subgroup.zpowers b)) = 4 := by
    rw [fixV_eq_commV_of_card hV2 hb2 hcard hcomm4']
    exact hcomm4'
  refine no_order_fifteen hV2 hcard hb2 hfixb hz hbz fun y hy hy3 hyb => ?_
  have hyF : y ∈ F := by rw [hFeq]; exact hy
  refine hstar y (hFX hyF) hy3 fun b' hb' => ?_
  rw [hBeq] at hb'
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
  exact ((Commute.zpow_left (show Commute b y from hyb) j)).eq

end S152N2

end CFSG.Quasithin
