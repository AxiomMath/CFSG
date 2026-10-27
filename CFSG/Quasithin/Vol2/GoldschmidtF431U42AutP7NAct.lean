module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5bBurn

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type*} [Group G]

@[expose] def Om (A : Subgroup G) (z : G) : Set G := {u | u ∈ A ∧ IsConj u z}

@[expose, instance_reducible] def conjAction (N : Subgroup G) : MulAction ↥N G where
  smul n g := (n : G) * g * (n : G)⁻¹
  one_smul g := by
    show ((1 : ↥N) : G) * g * ((1 : ↥N) : G)⁻¹ = g
    simp
  mul_smul a b g := by
    show ((a * b : ↥N) : G) * g * ((a * b : ↥N) : G)⁻¹ =
      (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group

theorem card_normalizer_eq [Finite G] {A : Subgroup G} {z : G} (hzA : z ∈ A)
    (htr : ∀ u ∈ A, IsConj u z → ∃ n ∈ Subgroup.normalizer (A : Set G), n * z * n⁻¹ = u) :
    Nat.card ↥(Subgroup.normalizer (A : Set G)) =
      (Om A z).ncard * Nat.card ↥(Subgroup.normalizer (A : Set G) ⊓
        Subgroup.centralizer ({z} : Set G)) := by
  set N := Subgroup.normalizer (A : Set G) with hN
  let inst : MulAction ↥N G := conjAction N
  have h1 := MulAction.index_stabilizer ↥N z
  have h2 := Subgroup.card_mul_index (MulAction.stabilizer ↥N z)
  have horb : MulAction.orbit ↥N z = Om A z := by
    ext u
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨n, rfl⟩
      show (n : G) * z * (n : G)⁻¹ ∈ A ∧ IsConj ((n : G) * z * (n : G)⁻¹) z
      refine ⟨(Subgroup.mem_normalizer_iff.1 n.2 z).1 hzA, isConj_iff.2 ⟨(n : G)⁻¹, ?_⟩⟩
      group
    · rintro ⟨huA, hu⟩
      obtain ⟨n, hn, hnz⟩ := htr u huA hu
      exact ⟨⟨n, hn⟩, hnz⟩
  have e : (N ⊓ Subgroup.centralizer ({z} : Set G)).subgroupOf N =
      MulAction.stabilizer ↥N z := by
    ext n
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    rw [MulAction.mem_stabilizer_iff]
    show _ ↔ (n : G) * z * (n : G)⁻¹ = z
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      rw [h]
      group
    · intro h
      refine ⟨n.2, ?_⟩
      calc (n : G) * z = ((n : G) * z * (n : G)⁻¹) * (n : G) := by group
        _ = z * (n : G) := by rw [h]
  have hstab : Nat.card ↥(MulAction.stabilizer ↥N z) =
      Nat.card ↥(N ⊓ Subgroup.centralizer ({z} : Set G)) := by
    rw [← e]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv)
  rw [h1, horb] at h2
  rw [← h2, hstab, mul_comm]

@[expose] def conjPermOf (N : Subgroup G) (X : Set G)
    (hX : ∀ n ∈ N, ∀ u ∈ X, n * u * n⁻¹ ∈ X) : ↥N →* Equiv.Perm ↥X where
  toFun n :=
    { toFun := fun u => ⟨(n : G) * u * (n : G)⁻¹, hX n n.2 u u.2⟩
      invFun := fun u => ⟨(n : G)⁻¹ * u * (n : G), by
        simpa using hX n⁻¹ (N.inv_mem n.2) u u.2⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext u
    simp
  map_mul' a b := by
    ext u
    simp [mul_assoc]

theorem mem_ker_conjPermOf {N : Subgroup G} {X : Set G} {hX : ∀ n ∈ N, ∀ u ∈ X, n * u * n⁻¹ ∈ X}
    {n : ↥N} : n ∈ (conjPermOf N X hX).ker ↔ ∀ u ∈ X, (n : G) * u = u * (n : G) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h u hu
    have := congrArg (fun p : Equiv.Perm ↥X => (p ⟨u, hu⟩ : G)) h
    simp only [conjPermOf, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk,
      Equiv.Perm.coe_one, id_eq] at this
    calc (n : G) * u = ((n : G) * u * (n : G)⁻¹) * (n : G) := by group
      _ = u * (n : G) := by rw [this]
  · intro h
    ext u
    simp only [conjPermOf, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk, Equiv.Perm.coe_one,
      id_eq]
    rw [h u u.2]
    group

theorem quotEquiv_of_ker {N P : Type*} [Group N] [Group P] [Finite N] [Finite P] (φ : N →* P)
    {K : Subgroup N} [K.Normal] (hker : φ.ker = K)
    (hcard : Nat.card N = Nat.card K * Nat.card P) : Nonempty (N ⧸ K ≃* P) := by
  subst hker
  have hinj := QuotientGroup.kerLift_injective φ
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have hq : Nat.card (N ⧸ φ.ker) = Nat.card P := by
    have hpos : 0 < Nat.card ↥φ.ker := Nat.card_pos
    rw [h1] at hcard
    exact Nat.eq_of_mul_eq_mul_right hpos (hcard.trans (mul_comm _ _))
  exact ⟨MulEquiv.ofBijective (QuotientGroup.kerLift φ)
    (hinj.bijective_of_nat_card_le hq.ge)⟩

theorem quot_equiv_perm [Finite G] {N A : Subgroup G} (hAN : A ≤ N) [(A.subgroupOf N).Normal]
    (X : Set G) (hX : ∀ n ∈ N, ∀ u ∈ X, n * u * n⁻¹ ∈ X)
    (hA : ∀ a ∈ A, ∀ u ∈ X, a * u = u * a)
    (hker : ∀ n ∈ N, (∀ u ∈ X, n * u = u * n) → n ∈ A) {m : ℕ} (hXm : Nat.card ↥X = m)
    (hcard : Nat.card ↥N = Nat.card ↥A * m.factorial) :
    Nonempty (↥N ⧸ A.subgroupOf N ≃* Equiv.Perm (Fin m)) := by
  have hk : (conjPermOf N X hX).ker = A.subgroupOf N := by
    ext n
    rw [mem_ker_conjPermOf, Subgroup.mem_subgroupOf]
    exact ⟨hker n n.2, fun h u hu => hA _ h u hu⟩
  have hc : Nat.card ↥N = Nat.card ↥(A.subgroupOf N) * Nat.card (Equiv.Perm ↥X) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv, hcard]
    have : Nat.card (Equiv.Perm ↥X) = m.factorial := by
      classical
      have := Fintype.ofFinite ↥X
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hXm]
    rw [this]
  obtain ⟨e⟩ := quotEquiv_of_ker (conjPermOf N X hX) hk hc
  exact ⟨e.trans (Finite.equivFinOfCardEq hXm).permCongrHom⟩

theorem quot_equiv_perm_prod [Finite G] {N A : Subgroup G} (hAN : A ≤ N)
    [(A.subgroupOf N).Normal] (X Y : Set G) (hX : ∀ n ∈ N, ∀ u ∈ X, n * u * n⁻¹ ∈ X)
    (hY : ∀ n ∈ N, ∀ u ∈ Y, n * u * n⁻¹ ∈ Y)
    (hA : ∀ a ∈ A, ∀ u ∈ X ∪ Y, a * u = u * a)
    (hker : ∀ n ∈ N, (∀ u ∈ X ∪ Y, n * u = u * n) → n ∈ A) {m m' : ℕ}
    (hXm : Nat.card ↥X = m) (hYm : Nat.card ↥Y = m')
    (hcard : Nat.card ↥N = Nat.card ↥A * (m.factorial * m'.factorial)) :
    Nonempty (↥N ⧸ A.subgroupOf N ≃* Equiv.Perm (Fin m) × Equiv.Perm (Fin m')) := by
  have hk : ((conjPermOf N X hX).prod (conjPermOf N Y hY)).ker = A.subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : n ∈ (conjPermOf N X hX).ker := congrArg Prod.fst h
      have h2 : n ∈ (conjPermOf N Y hY).ker := congrArg Prod.snd h
      rw [mem_ker_conjPermOf] at h1 h2
      refine hker n n.2 fun u hu => ?_
      rcases hu with hu | hu
      · exact h1 u hu
      · exact h2 u hu
    · intro h
      refine Prod.ext ?_ ?_
      · have : n ∈ (conjPermOf N X hX).ker :=
          mem_ker_conjPermOf.2 fun u hu => hA _ h u (Or.inl hu)
        exact this
      · have : n ∈ (conjPermOf N Y hY).ker :=
          mem_ker_conjPermOf.2 fun u hu => hA _ h u (Or.inr hu)
        exact this
  have hc : Nat.card ↥N = Nat.card ↥(A.subgroupOf N) *
      Nat.card (Equiv.Perm ↥X × Equiv.Perm ↥Y) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv, hcard, Nat.card_prod]
    have h1 : Nat.card (Equiv.Perm ↥X) = m.factorial := by
      classical
      have := Fintype.ofFinite ↥X
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hXm]
    have h2 : Nat.card (Equiv.Perm ↥Y) = m'.factorial := by
      classical
      have := Fintype.ofFinite ↥Y
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hYm]
    rw [h1, h2]
  obtain ⟨e⟩ := quotEquiv_of_ker ((conjPermOf N X hX).prod (conjPermOf N Y hY)) hk hc
  exact ⟨e.trans (MulEquiv.prodCongr (Finite.equivFinOfCardEq hXm).permCongrHom
    (Finite.equivFinOfCardEq hYm).permCongrHom)⟩


end CFSG.Quasithin.H13.F431.U42Aut
