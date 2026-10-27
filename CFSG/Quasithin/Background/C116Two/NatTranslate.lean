module

public import CFSG.Quasithin.Background.C116Two.Kernel

public section

namespace CFSG.Quasithin.C116Two

open CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {V : Type} [CommGroup V]

@[expose] def conjU (L : Subgroup G) {b : G} (hb : b ∈ Subgroup.normalizer (L : Set G)) :
    ↥(blockU L) →* ↥(blockU L) where
  toFun u := ⟨b * u * b⁻¹,
    (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU hb) u).mp u.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (by simp [mul_assoc])

theorem conjU_apply (L : Subgroup G) {b : G} (hb : b ∈ Subgroup.normalizer (L : Set G))
    (u : ↥(blockU L)) : ((conjU L hb u : ↥(blockU L)) : G) = b * u * b⁻¹ := rfl

theorem beta_eq_iff_mem_blockZ (D : ModData L V) (u v : ↥(blockU L)) :
    D.β u = D.β v ↔ ((u * v⁻¹ : ↥(blockU L)) : G) ∈ blockZ L := by
  rw [← Subgroup.mem_subgroupOf, ← D.ker, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]

theorem beta_eq_one_iff (D : ModData L V) (u : ↥(blockU L)) :
    D.β u = 1 ↔ (u : G) ∈ blockZ L := by
  rw [← MonoidHom.mem_ker, D.ker, Subgroup.mem_subgroupOf]

theorem beta_conjU_of_beta_eq (D : ModData L V) (b : ↥(Subgroup.normalizer (L : Set G)))
    {u v : ↥(blockU L)} (h : D.β u = D.β v) :
    D.β (conjU L b.2 u) = D.β (conjU L b.2 v) := by
  rw [beta_eq_iff_mem_blockZ] at h ⊢
  have e : conjU L b.2 (u * v⁻¹) = conjU L b.2 u * (conjU L b.2 v)⁻¹ := by
    rw [map_mul, map_inv]
  rw [← e, conjU_apply]
  exact (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockZ b.2) _).mp h

theorem conjL_mem_blockU (ℓ : ↥L) (x : ↥(blockU L)) :
    (ℓ : G) * (x : G) * (ℓ : G)⁻¹ ∈ blockU L :=
  (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU L ℓ.2) (x : G)).mp x.2

noncomputable def descAct (D : ModData L V) (b : ↥(Subgroup.normalizer (L : Set G))) (v : V) : V :=
  D.β (conjU L b.2 (Function.surjInv D.surj v))

theorem descAct_beta (D : ModData L V) (b : ↥(Subgroup.normalizer (L : Set G)))
    (u : ↥(blockU L)) : descAct D b (D.β u) = D.β (conjU L b.2 u) :=
  beta_conjU_of_beta_eq D b (Function.surjInv_eq D.surj (D.β u))

theorem descAct_one (D : ModData L V) (v : V) : descAct D 1 v = v := by
  obtain ⟨u, rfl⟩ := D.surj v
  rw [descAct_beta]
  congr 1
  exact Subtype.ext (by simp [conjU_apply])

theorem descAct_mul (D : ModData L V) (b b' : ↥(Subgroup.normalizer (L : Set G))) (v : V) :
    descAct D (b * b') v = descAct D b (descAct D b' v) := by
  obtain ⟨u, rfl⟩ := D.surj v
  simp only [descAct_beta]
  congr 1
  exact Subtype.ext (by simp [conjU_apply, mul_assoc])

noncomputable def descAut (D : ModData L V) (b : ↥(Subgroup.normalizer (L : Set G))) :
    MulAut V where
  toFun := descAct D b
  invFun := descAct D b⁻¹
  left_inv v := by
    show descAct D b⁻¹ (descAct D b v) = v
    rw [← descAct_mul, inv_mul_cancel, descAct_one]
  right_inv v := by
    show descAct D b (descAct D b⁻¹ v) = v
    rw [← descAct_mul, mul_inv_cancel, descAct_one]
  map_mul' v w := by
    show descAct D b (v * w) = descAct D b v * descAct D b w
    obtain ⟨x, rfl⟩ := D.surj v
    obtain ⟨y, rfl⟩ := D.surj w
    rw [← map_mul D.β, descAct_beta, descAct_beta, descAct_beta, map_mul (conjU L b.2),
      map_mul D.β]

theorem exists_conjAut (D : ModData L V) :
    ∃ Φ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut V,
      ∀ (b : ↥(Subgroup.normalizer (L : Set G))) (u : ↥(blockU L)),
        Φ b (D.β u) = D.β (conjU L b.2 u) :=
  ⟨{ toFun := descAut D
     map_one' := MulEquiv.ext fun v => descAct_one D v
     map_mul' := fun b b' => MulEquiv.ext fun v => descAct_mul D b b' v },
   fun b u => descAct_beta D b u⟩

theorem beta_rho_conj (D : ModData L V) (ℓ : ↥L) (x : ↥(blockU L)) :
    D.ρ ℓ (D.β x) = D.β ⟨(ℓ : G) * x * (ℓ : G)⁻¹, conjL_mem_blockU ℓ x⟩ :=
  (D.equiv ℓ x ⟨(ℓ : G) * x * (ℓ : G)⁻¹, conjL_mem_blockU ℓ x⟩ rfl).symm

theorem comm_mem_blockZ_iff (D : ModData L V)
    {Φ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut V}
    (hΦ : ∀ (b : ↥(Subgroup.normalizer (L : Set G))) (u : ↥(blockU L)),
      Φ b (D.β u) = D.β (conjU L b.2 u))
    (b : ↥(Subgroup.normalizer (L : Set G))) (u : ↥(blockU L)) :
    ⁅(u : G), (b : G)⁆ ∈ blockZ L ↔ Φ b (D.β u) = D.β u := by
  rw [hΦ, beta_eq_iff_mem_blockZ]
  have e : ((conjU L b.2 u * u⁻¹ : ↥(blockU L)) : G) = ⁅(u : G), (b : G)⁆⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, conjU_apply, commutatorElement_def]
    group
  rw [e, Subgroup.inv_mem_iff]

theorem conjAut_normalizes (D : ModData L V)
    {Φ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut V}
    (hΦ : ∀ (b : ↥(Subgroup.normalizer (L : Set G))) (u : ↥(blockU L)),
      Φ b (D.β u) = D.β (conjU L b.2 u))
    (b : ↥(Subgroup.normalizer (L : Set G))) (ℓ : ↥L) :
    Φ b * D.ρ ℓ * (Φ b)⁻¹ =
      D.ρ ⟨(b : G) * ℓ * (b : G)⁻¹, (Subgroup.mem_normalizer_iff.mp b.2 ℓ).mp ℓ.2⟩ := by
  have key : ∀ ℓ' : ↥L, (ℓ' : G) = (b : G) * ℓ * (b : G)⁻¹ →
      Φ b * D.ρ ℓ = D.ρ ℓ' * Φ b := by
    intro ℓ' hℓ'
    refine MulEquiv.ext fun v => ?_
    obtain ⟨x, rfl⟩ := D.surj v
    rw [MulAut.mul_apply, MulAut.mul_apply, beta_rho_conj D ℓ x, hΦ, hΦ,
      beta_rho_conj D ℓ' (conjU L b.2 x)]
    congr 1
    exact Subtype.ext (by simp only [conjU_apply, hℓ']; group)
  rw [key ⟨(b : G) * ℓ * (b : G)⁻¹, (Subgroup.mem_normalizer_iff.mp b.2 ℓ).mp ℓ.2⟩ rfl,
    mul_assoc, mul_inv_cancel, mul_one]

theorem conjAut_eq_one_iff (D : ModData L V)
    {Φ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut V}
    (hΦ : ∀ (b : ↥(Subgroup.normalizer (L : Set G))) (u : ↥(blockU L)),
      Φ b (D.β u) = D.β (conjU L b.2 u))
    (b : ↥(Subgroup.normalizer (L : Set G))) :
    Φ b = 1 ↔ ∀ u ∈ blockU L, ⁅u, (b : G)⁆ ∈ blockZ L := by
  constructor
  · intro h u hu
    refine (comm_mem_blockZ_iff D hΦ b ⟨u, hu⟩).mpr ?_
    rw [h, MulAut.one_apply]
  · intro h
    refine MulEquiv.ext fun v => ?_
    obtain ⟨x, rfl⟩ := D.surj v
    rw [MulAut.one_apply]
    exact (comm_mem_blockZ_iff D hΦ b x).mp (h (x : G) x.2)

theorem card_blockU_eq (D : ModData L V) :
    Nat.card ↥(blockU L) = Nat.card ↥(blockZ L) * Nat.card V := by
  have hZU : blockZ L ≤ blockU L := inf_le_left
  have h1 : Nat.card ↥(blockU L) =
      Nat.card (↥(blockU L) ⧸ D.β.ker) * Nat.card ↥(D.β.ker) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h2 : Nat.card (↥(blockU L) ⧸ D.β.ker) = Nat.card V :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective D.β D.surj).toEquiv
  have h3 : Nat.card ↥(D.β.ker) = Nat.card ↥(blockZ L) := by
    rw [D.ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv
  rw [h1, h2, h3, mul_comm]

theorem card_fixSet_eq (D : ModData L V)
    {Φ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut V}
    (hΦ : ∀ (b : ↥(Subgroup.normalizer (L : Set G))) (u : ↥(blockU L)),
      Φ b (D.β u) = D.β (conjU L b.2 u))
    (B : Subgroup G) (hBN : B ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card {u : G // u ∈ blockU L ∧ ∀ b ∈ B, ⁅u, b⁆ ∈ blockZ L} =
      Nat.card ↥(blockZ L) * Nat.card {x : V // ∀ b : ↥B, Φ ⟨b, hBN b.2⟩ x = x} := by
  have hZU : blockZ L ≤ blockU L := inf_le_left
  have memS : ∀ u : ↥(blockU L), (∀ b ∈ B, ⁅(u : G), b⁆ ∈ blockZ L) ↔
      ∀ b : ↥B, Φ ⟨(b : G), hBN b.2⟩ (D.β u) = D.β u := by
    intro u
    constructor
    · intro h b
      exact (comm_mem_blockZ_iff D hΦ ⟨(b : G), hBN b.2⟩ u).mp (h b b.2)
    · intro h b hb
      exact (comm_mem_blockZ_iff D hΦ ⟨b, hBN hb⟩ u).mpr (h ⟨b, hb⟩)
  have hβσ : ∀ x : V, D.β (Function.surjInv D.surj x) = x := Function.surjInv_eq D.surj
  have hliftβ : ∀ (z : ↥(blockZ L)) (x : V),
      D.β (Function.surjInv D.surj x * ⟨(z : G), hZU z.2⟩) = x := by
    intro z x
    rw [map_mul, (beta_eq_one_iff D ⟨(z : G), hZU z.2⟩).mpr z.2, mul_one, hβσ x]
  have hmemS : ∀ (z : ↥(blockZ L)) (x : {x : V // ∀ b : ↥B, Φ ⟨b, hBN b.2⟩ x = x}),
      ∀ b ∈ B, ⁅((Function.surjInv D.surj x.1 * ⟨(z : G), hZU z.2⟩ : ↥(blockU L)) : G), b⁆
        ∈ blockZ L := by
    intro z x
    refine (memS (Function.surjInv D.surj x.1 * ⟨(z : G), hZU z.2⟩)).mpr fun b => ?_
    rw [hliftβ z x.1]
    exact x.2 b
  rw [← Nat.card_prod]
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : ↥(blockZ L) × {x : V // ∀ b : ↥B, Φ ⟨b, hBN b.2⟩ x = x} =>
      (⟨((Function.surjInv D.surj p.2.1 * ⟨(p.1 : G), hZU p.1.2⟩ : ↥(blockU L)) : G),
        (Function.surjInv D.surj p.2.1 * ⟨(p.1 : G), hZU p.1.2⟩ : ↥(blockU L)).2,
        hmemS p.1 p.2⟩ :
        {u : G // u ∈ blockU L ∧ ∀ b ∈ B, ⁅u, b⁆ ∈ blockZ L}))
    ⟨?_, ?_⟩).symm
  · rintro ⟨z1, x1⟩ ⟨z2, x2⟩ h
    have h' := congrArg Subtype.val h
    have hu : (Function.surjInv D.surj x1.1 * ⟨(z1 : G), hZU z1.2⟩ : ↥(blockU L)) =
        Function.surjInv D.surj x2.1 * ⟨(z2 : G), hZU z2.2⟩ := Subtype.ext h'
    have hx : x1.1 = x2.1 := by
      have := congrArg D.β hu
      rwa [hliftβ, hliftβ] at this
    have hx' : x1 = x2 := Subtype.ext hx
    subst hx'
    have hz : (⟨(z1 : G), hZU z1.2⟩ : ↥(blockU L)) = ⟨(z2 : G), hZU z2.2⟩ :=
      mul_left_cancel hu
    have hz' := congrArg Subtype.val hz
    have hz'' : z1 = z2 := Subtype.ext hz'
    subst hz''
    rfl
  · rintro ⟨u, hu⟩
    obtain ⟨w, rfl⟩ : ∃ w : ↥(blockU L), (w : G) = u := ⟨⟨u, hu.1⟩, rfl⟩
    have hxT : ∀ b : ↥B, Φ ⟨(b : G), hBN b.2⟩ (D.β w) = D.β w := (memS w).mp hu.2
    have hz0 : (((Function.surjInv D.surj (D.β w))⁻¹ * w : ↥(blockU L)) : G) ∈ blockZ L := by
      refine (beta_eq_one_iff D _).mp ?_
      rw [map_mul, map_inv, hβσ, inv_mul_cancel]
    have e : Function.surjInv D.surj (D.β w) *
        (⟨(((Function.surjInv D.surj (D.β w))⁻¹ * w : ↥(blockU L)) : G), hZU hz0⟩ : ↥(blockU L)) = w :=
      mul_inv_cancel_left (Function.surjInv D.surj (D.β w)) w
    refine ⟨(⟨(((Function.surjInv D.surj (D.β w))⁻¹ * w : ↥(blockU L)) : G), hz0⟩,
      ⟨D.β w, hxT⟩), ?_⟩
    apply Subtype.ext
    show (((Function.surjInv D.surj (D.β w) *
        (⟨(((Function.surjInv D.surj (D.β w))⁻¹ * w : ↥(blockU L)) : G), hZU hz0⟩ : ↥(blockU L))) :
        ↥(blockU L)) : G) = (w : G)
    rw [e]

theorem relIndex_eq_card_range (hL : IsShort2 L) (D : ModData L V)
    {Φ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut V}
    (hΦ : ∀ (b : ↥(Subgroup.normalizer (L : Set G))) (u : ↥(blockU L)),
      Φ b (D.β u) = D.β (conjU L b.2 u))
    (B : Subgroup G) (hBN : B ≤ Subgroup.normalizer (L : Set G)) :
    (B ⊓ Subgroup.centralizer (blockU L : Set G)).relIndex B =
      Nat.card (Φ.comp (Subgroup.inclusion hBN)).range := by
  have key : ∀ b : ↥B, Φ ⟨(b : G), hBN b.2⟩ = 1 ↔
      ∀ u ∈ blockU L, u * (b : G) = (b : G) * u := by
    intro b
    rw [conjAut_eq_one_iff D hΦ ⟨(b : G), hBN b.2⟩]
    constructor
    · intro h u hu
      exact commutatorElement_eq_one_iff_mul_comm.mp (kernel_lemma D hL (hBN b.2) h u hu)
    · intro h u hu
      have h1 : ⁅u, (b : G)⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (h u hu)
      show ⁅u, (b : G)⁆ ∈ blockZ L
      rw [h1]
      exact Subgroup.one_mem _
  have hker : (Φ.comp (Subgroup.inclusion hBN)).ker =
      (B ⊓ Subgroup.centralizer (blockU L : Set G)).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    change Φ ⟨(b : G), hBN b.2⟩ = 1 ↔
      (b : G) ∈ B ∧ (b : G) ∈ Subgroup.centralizer (blockU L : Set G)
    rw [key b, Subgroup.mem_centralizer_iff]
    exact ⟨fun h => ⟨b.2, fun u hu => h u hu⟩, fun h => h.2⟩
  show ((B ⊓ Subgroup.centralizer (blockU L : Set G)).subgroupOf B).index = _
  rw [← hker, Subgroup.index_ker]

theorem natCount_of_modData [Finite V] (hL : IsShort2 L) (D : ModData L V) {B : Subgroup G}
    (hB : IsElemAbelian 2 B) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hN : NatCountMod V D.ρ.range) :
    (B ⊓ Subgroup.centralizer (blockU L : Set G)).relIndex B *
        Nat.card {u : G // u ∈ blockU L ∧ ∀ b ∈ B, ⁅u, b⁆ ∈ blockZ L} ≤
      Nat.card (blockU L) := by
  obtain ⟨Φ, hΦ⟩ := exists_conjAut D
  set Φ' : ↥B →* MulAut V := Φ.comp (Subgroup.inclusion hBN) with hΦ'
  have h1 := relIndex_eq_card_range hL D hΦ B hBN
  have h2 := card_fixSet_eq D hΦ B hBN
  have h3 := card_blockU_eq D
  have hEA : IsElemAbelian 2 Φ'.range := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := x.2
      obtain ⟨b, hb⟩ := y.2
      apply Subtype.ext
      have hab : a * b = b * a := Subtype.ext (by
        have := hB.1.is_comm.comm a b
        exact congrArg Subtype.val this)
      show (x : MulAut V) * y = y * x
      rw [← ha, ← hb, ← map_mul, ← map_mul, hab]
    · obtain ⟨a, rfl⟩ := hx
      rw [← map_pow]
      have : a ^ 2 = 1 := Subtype.ext (by simpa using hB.2 (a : G) a.2)
      rw [this, map_one]
  have hNorm : ∀ b ∈ Φ'.range, ∀ l ∈ D.ρ.range, b * l * b⁻¹ ∈ D.ρ.range := by
    rintro _ ⟨a, rfl⟩ _ ⟨ℓ, rfl⟩
    refine ⟨_, (conjAut_normalizes D hΦ ⟨(a : G), hBN a.2⟩ ℓ).symm⟩
  have h4 := hN Φ'.range hEA hNorm
  have h5 : Nat.card {x : V // ∀ b ∈ Φ'.range, b x = x} =
      Nat.card {x : V // ∀ b : ↥B, Φ ⟨b, hBN b.2⟩ x = x} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    constructor
    · intro h b
      exact h _ ⟨b, rfl⟩
    · rintro h _ ⟨b, rfl⟩
      exact h b
  rw [h5] at h4
  rw [h1, h2, h3]
  calc Nat.card Φ'.range * (Nat.card ↥(blockZ L) *
        Nat.card {x : V // ∀ b : ↥B, Φ ⟨b, hBN b.2⟩ x = x})
      = Nat.card ↥(blockZ L) * (Nat.card Φ'.range *
        Nat.card {x : V // ∀ b : ↥B, Φ ⟨b, hBN b.2⟩ x = x}) := by ring
    _ ≤ Nat.card ↥(blockZ L) * Nat.card V := Nat.mul_le_mul_left _ h4

end CFSG.Quasithin.C116Two
