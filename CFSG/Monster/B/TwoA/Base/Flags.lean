module

public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Monster.B.TwoA.Base.Subspaces
public import CFSG.Monster.B.TwoA.Base.GroupAux

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG Module

open scoped IsMulCommutative

theorem mem_normalizer_iff_conjE {G : Type*} [Group G] [Finite G] {E F : Subgroup G}
    (hFE : F ≤ E) (g : Subgroup.normalizer (E : Set G)) :
    (g : G) ∈ Subgroup.normalizer (F : Set G) ↔
      ∀ e : E, (e : G) ∈ F → ((conjE E g e : E) : G) ∈ F := by
  constructor
  · intro h e he
    rw [coe_conjE]
    exact conj_mem_of_normalizer h he
  · intro h
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    exact h ⟨n, hFE hn⟩ hn

theorem le_of_natCard_pow {G : Type*} [Group G] [Finite G] {E F : Subgroup G} {n j : ℕ}
    (hE : Nat.card E = 2 ^ n) (hF : Nat.card F = 2 ^ j) (hFE : F ≤ E) : j ≤ n := by
  have h1 := Subgroup.card_le_of_le hFE
  rw [hE, hF] at h1
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1

theorem index_eq_of_natCard {G : Type*} [Group G] {H K : Subgroup G} (hle : H ≤ K) {a b c : ℕ}
    (ha : Nat.card H = a) (hb : Nat.card K = b) (hpos : 0 < a) (hc : b = a * c) :
    (H.subgroupOf K).index = c := by
  have h := (H.subgroupOf K).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, ha, hb, hc] at h
  exact Nat.eq_of_mul_eq_mul_left hpos h

theorem lt_of_le_of_natCard_lt {G : Type*} [Group G] {H K : Subgroup G} (hle : H ≤ K)
    (hc : Nat.card H < Nat.card K) : H < K :=
  lt_of_le_of_ne hle fun e => by
    rw [e] at hc
    exact lt_irrefl _ hc

section Sub

variable {G : Type*} [Group G] (E : Subgroup G) [CFSG.IsElementaryAbelian 2 E]

@[expose] def addSubOf (F : Subgroup G) : AddSubgroup (Additive E) where
  carrier := {x | ((Additive.toMul x : E) : G) ∈ F}
  add_mem' {a b} ha hb := by
    change ((Additive.toMul a : E) : G) * ((Additive.toMul b : E) : G) ∈ F
    exact F.mul_mem ha hb
  zero_mem' := F.one_mem
  neg_mem' {a} ha := by
    change ((Additive.toMul a : E) : G)⁻¹ ∈ F
    exact F.inv_mem ha

@[expose] noncomputable def subOf (F : Subgroup G) : Submodule (ZMod 2) (Additive E) :=
  AddSubgroup.toZModSubmodule 2 (addSubOf E F)

theorem mem_subOf {F : Subgroup G} {x : Additive E} :
    x ∈ subOf E F ↔ ((Additive.toMul x : E) : G) ∈ F := Iff.rfl

theorem natCard_subOf {F : Subgroup G} (hFE : F ≤ E) : Nat.card (subOf E F) = Nat.card F :=
  Nat.card_congr
    { toFun := fun x => ⟨((Additive.toMul x.1 : E) : G), x.2⟩
      invFun := fun f => ⟨Additive.ofMul ⟨f, hFE f.2⟩, f.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem finrank_subOf [Finite G] {F : Subgroup G} (hFE : F ≤ E) {j : ℕ} (hF : Nat.card F = 2 ^ j) :
    finrank (ZMod 2) (subOf E F) = j := by
  have h := FiniteField.pow_finrank_eq_natCard 2 (subOf E F)
  rw [natCard_subOf E hFE, hF] at h
  exact Nat.pow_right_injective le_rfl h

@[expose] noncomputable def linConj : Subgroup.normalizer (E : Set G) →*
    (Additive E ≃ₗ[ZMod 2] Additive E) :=
  (mulAutEquivLinear E).toMonoidHom.comp (conjE E)

theorem linConj_apply (g : Subgroup.normalizer (E : Set G)) (e : E) :
    ((Additive.toMul (linConj E g (Additive.ofMul e)) : E) : G) = (g : G) * e * (g : G)⁻¹ :=
  rfl

theorem linConj_surjective (h : Function.Surjective (conjE E)) :
    Function.Surjective (linConj E) := by
  rw [linConj, MonoidHom.coe_comp]
  exact (MulEquiv.surjective _).comp h

theorem map_linConj_le_iff {F : Subgroup G} (hFE : F ≤ E) (g : Subgroup.normalizer (E : Set G)) :
    (subOf E F).map (linConj E g : Additive E →ₗ[ZMod 2] Additive E) ≤ subOf E F ↔
      ∀ f ∈ F, (g : G) * f * (g : G)⁻¹ ∈ F := by
  constructor
  · intro h f hf
    have h1 : (linConj E g : Additive E →ₗ[ZMod 2] Additive E) (Additive.ofMul ⟨f, hFE hf⟩) ∈
        subOf E F := h ⟨_, hf, rfl⟩
    exact h1
  · rintro h _ ⟨x, hx, rfl⟩
    exact h _ hx

theorem map_linConj_eq_iff [Finite G] {F : Subgroup G} (hFE : F ≤ E)
    (g : Subgroup.normalizer (E : Set G)) :
    (subOf E F).map (linConj E g : Additive E →ₗ[ZMod 2] Additive E) = subOf E F ↔
      (g : G) ∈ Subgroup.normalizer (F : Set G) := by
  constructor
  · intro h
    refine Subgroup.mem_normalizer_fintype fun f hf => ?_
    exact (map_linConj_le_iff E hFE g).1 h.le f hf
  · intro h
    refine Submodule.eq_of_le_of_finrank_eq ((map_linConj_le_iff E hFE g).2 fun f hf =>
      conj_mem_of_normalizer h hf) ?_
    exact LinearEquiv.finrank_map_eq _ _

end Sub

section Action

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

@[expose, instance_reducible] noncomputable def subspaceAction (j : ℕ) :
    MulAction (V ≃ₗ[K] V) (SubspaceDim K V j) where
  smul e S := ⟨S.1.map (e : V →ₗ[K] V), by rw [LinearEquiv.finrank_map_eq]; exact S.2⟩
  one_smul S := Subtype.ext (by
    change S.1.map ((1 : V ≃ₗ[K] V) : V →ₗ[K] V) = S.1
    exact Submodule.map_id S.1)
  mul_smul e f S := Subtype.ext (by
    change S.1.map ((e * f : V ≃ₗ[K] V) : V →ₗ[K] V) =
      (S.1.map (f : V →ₗ[K] V)).map (e : V →ₗ[K] V)
    rw [← Submodule.map_comp]
    rfl)

end Action

attribute [local instance] subspaceAction

theorem index_normalizer_inf {G : Type*} [Group G] [Finite G] {E F : Subgroup G}
    [CFSG.IsElementaryAbelian 2 E] {n j : ℕ} (hE : Nat.card E = 2 ^ n) (hF : Nat.card F = 2 ^ j)
    (hFE : F ≤ E) (hsurj : Function.Surjective (conjE E)) :
    ((Subgroup.normalizer (F : Set G) ⊓ Subgroup.normalizer (E : Set G)).subgroupOf
      (Subgroup.normalizer (E : Set G))).index = qBinom 2 n j := by
  have hn : finrank (ZMod 2) (Additive E) = n := finrank_additive_of_card hE
  have hjn : j ≤ n := le_of_natCard_pow hE hF hFE
  let : MulAction (Subgroup.normalizer (E : Set G)) (SubspaceDim (ZMod 2) (Additive E) j) :=
    MulAction.compHom _ (linConj E)
  set S₀ : SubspaceDim (ZMod 2) (Additive E) j := ⟨subOf E F, finrank_subOf E hFE hF⟩
  have hstab : MulAction.stabilizer (Subgroup.normalizer (E : Set G)) S₀ =
      (Subgroup.normalizer (F : Set G) ⊓ Subgroup.normalizer (E : Set G)).subgroupOf
        (Subgroup.normalizer (E : Set G)) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      ← Subtype.coe_inj]
    change (subOf E F).map (linConj E g : Additive E →ₗ[ZMod 2] Additive E) = subOf E F ↔ _
    rw [map_linConj_eq_iff E hFE g]
    exact ⟨fun h => ⟨h, g.2⟩, fun h => h.1⟩
  have horb : MulAction.orbit (Subgroup.normalizer (E : Set G)) S₀ = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro T
    obtain ⟨e, he⟩ := exists_linearEquiv_map_eq (S := S₀.1) (T := T.1) (by rw [S₀.2, T.2])
    obtain ⟨g, hg⟩ := linConj_surjective E hsurj e
    refine ⟨g, Subtype.ext ?_⟩
    change S₀.1.map (linConj E g : Additive E →ₗ[ZMod 2] Additive E) = T.1
    rw [hg, he]
  rw [← hstab, MulAction.index_stabilizer, horb, Set.ncard_univ,
    card_subspaces (by rw [hn]; exact hjn), ZMod.card, hn]

theorem flag_pair {G : Type*} [Group G] [Finite G] {E F : Subgroup G}
    [CFSG.IsElementaryAbelian 2 E] {n j : ℕ} (hE : Nat.card E = 2 ^ n) (hF : Nat.card F = 2 ^ j)
    (hFE : F ≤ E) (hsurj : Function.Surjective (conjE E)) :
    (∀ g : Subgroup.normalizer (E : Set G), (g : G) ∈ Subgroup.normalizer (F : Set G) ↔
      ∀ e : E, (e : G) ∈ F → ((conjE E g e : E) : G) ∈ F) ∧
    ((Subgroup.normalizer (F : Set G) ⊓ Subgroup.normalizer (E : Set G)).subgroupOf
      (Subgroup.normalizer (E : Set G))).index =
        Nat.card (SubspaceDim (ZMod 2) (Fin n → ZMod 2) j) := by
  refine ⟨mem_normalizer_iff_conjE hFE, ?_⟩
  rw [index_normalizer_inf hE hF hFE hsurj,
    card_subspaces (by rw [Module.finrank_fin_fun]; exact le_of_natCard_pow hE hF hFE), ZMod.card,
    Module.finrank_fin_fun]

attribute [local instance] sharpAction

theorem pCore_normalizer_le_centralizer {G : Type*} [Group G] [Finite G] {E : Subgroup G} {p : ℕ}
    [Fact p.Prime] (hp : ¬ p ∣ Nat.card E - 1) {x0 : G}
    (htr : ∀ a ∈ E, a ≠ 1 → ∃ g ∈ Subgroup.normalizer (E : Set G), g * x0 * g⁻¹ = a) :
    CFSG.pCore p (Subgroup.normalizer (E : Set G)) ≤
      (Subgroup.centralizer (E : Set G)).subgroupOf (Subgroup.normalizer (E : Set G)) := by
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := p)
    (G := Subgroup.normalizer (E : Set G))).nonempty_fixed_point_of_prime_not_dvd_card
      (Esharp E) (by rw [natCard_Esharp]; exact hp)
  obtain ⟨ka, hka, hkax⟩ := htr a.1 a.2.1 a.2.2
  intro q hq
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  intro e he
  by_cases he1 : e = 1
  · rw [he1, one_mul, mul_one]
  obtain ⟨kb, hkb, hkbx⟩ := htr e he he1
  let k : Subgroup.normalizer (E : Set G) :=
    ⟨kb, hkb⟩ * (⟨ka, hka⟩ : Subgroup.normalizer (E : Set G))⁻¹
  have hk : (k : G) * a * (k : G)⁻¹ = e := by
    change kb * ka⁻¹ * a * (kb * ka⁻¹)⁻¹ = e
    rw [← hkax, ← hkbx]
    group
  let r : Subgroup.normalizer (E : Set G) := k⁻¹ * q * k
  have hr : r ∈ CFSG.pCore p (Subgroup.normalizer (E : Set G)) := by
    have h := (CFSG.pCore_normal (p := p)
      (G := Subgroup.normalizer (E : Set G))).conj_mem q hq k⁻¹
    rwa [inv_inv] at h
  have hra : (r : G) * a * (r : G)⁻¹ = a := congrArg Subtype.val (ha ⟨r, hr⟩)
  have hqe : (q : G) * e * (q : G)⁻¹ = e := by
    rw [← hk]
    calc (q : G) * ((k : G) * a * (k : G)⁻¹) * (q : G)⁻¹
        = (k : G) * ((r : G) * a * (r : G)⁻¹) * (k : G)⁻¹ := by
          change (q : G) * ((k : G) * a * (k : G)⁻¹) * (q : G)⁻¹ =
            (k : G) * ((k : G)⁻¹ * q * k * a * ((k : G)⁻¹ * q * k)⁻¹) * (k : G)⁻¹
          group
      _ = (k : G) * a * (k : G)⁻¹ := by rw [hra]
  rw [mul_inv_eq_iff_eq_mul] at hqe
  exact hqe.symm

theorem pCore_normalizer_eq_centralizer {G : Type*} [Group G] [Finite G] {E : Subgroup G} {p : ℕ}
    [Fact p.Prime] (hC : IsPGroup p (Subgroup.centralizer (E : Set G)))
    (hp : ¬ p ∣ Nat.card E - 1) {x0 : G}
    (htr : ∀ a ∈ E, a ≠ 1 → ∃ g ∈ Subgroup.normalizer (E : Set G), g * x0 * g⁻¹ = a) :
    CFSG.pCore p (Subgroup.normalizer (E : Set G)) =
      (Subgroup.centralizer (E : Set G)).subgroupOf (Subgroup.normalizer (E : Set G)) :=
  le_antisymm (pCore_normalizer_le_centralizer hp htr)
    (le_pCore_of_normal (ker_conjE E ▸ (conjE E).normal_ker) hC.comap_subtype)

end CFSG.Monster.B.TwoA
