module

public import CFSG.LocalAnalysis.StandardType.FS81.NoTransvSylow

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

variable {G : Type} [Group G]

structure TransvSetup [Finite G] (b₀ : G) (K E : Subgroup G) : Prop where
  ord : orderOf b₀ = 3
  elem : IsElemAbelian 3 E
  sup : Subgroup.zpowers b₀ ⊔ (E ⊓ K) = E
  disj : Disjoint (Subgroup.zpowers b₀) (E ⊓ K)
  inv : ∀ g ∈ Subgroup.normalizer (E : Set G), ∀ a ∈ E ⊓ K, g * a * g⁻¹ ∈ E ⊓ K
  transv : ∀ β ∈ E ⊓ K, ∃ g ∈ Subgroup.normalizer (E : Set G),
    (∀ a ∈ E ⊓ K, g * a * g⁻¹ = a) ∧ g * b₀ * g⁻¹ = b₀ * β
  syl : ∀ y ∈ Subgroup.centralizer (E : Set G), ∀ k : ℕ, y ^ 3 ^ k = 1 → y ∈ E

@[expose] def transvN1 (b₀ : G) (K E : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (E : Set G) ∧ (∀ a ∈ E ⊓ K, g * a * g⁻¹ = a) ∧
    b₀⁻¹ * (g * b₀ * g⁻¹) ∈ E ⊓ K}
  mul_mem' := fun {g h} hg hh => by
    obtain ⟨hgN, hgA, hgb⟩ := hg
    obtain ⟨hhN, hhA, hhb⟩ := hh
    refine ⟨Subgroup.mul_mem _ hgN hhN, fun a ha => ?_, ?_⟩
    · rw [show g * h * a * (g * h)⁻¹ = g * (h * a * h⁻¹) * g⁻¹ by group, hhA a ha, hgA a ha]
    · have h1 : g * h * b₀ * (g * h)⁻¹ = g * b₀ * g⁻¹ * (g * (b₀⁻¹ * (h * b₀ * h⁻¹)) * g⁻¹) := by
        group
      rw [h1, hgA _ hhb, ← mul_assoc]
      exact Subgroup.mul_mem _ hgb hhb
  one_mem' := ⟨Subgroup.one_mem _, fun a _ => by group, by
    rw [one_mul, inv_one, mul_one, inv_mul_cancel]; exact Subgroup.one_mem _⟩
  inv_mem' := fun {g} hg => by
    obtain ⟨hgN, hgA, hgb⟩ := hg
    have hgA' : ∀ a ∈ E ⊓ K, g⁻¹ * a * g⁻¹⁻¹ = a := fun a ha => by
      have := hgA a ha
      rw [inv_inv]
      calc g⁻¹ * a * g = g⁻¹ * (g * a * g⁻¹) * g := by rw [this]
        _ = a := by group
    refine ⟨Subgroup.inv_mem _ hgN, hgA', ?_⟩
    have h1 : b₀⁻¹ * (g⁻¹ * b₀ * g⁻¹⁻¹) = g⁻¹ * (b₀⁻¹ * (g * b₀ * g⁻¹))⁻¹ * g⁻¹⁻¹ := by group
    rw [h1, hgA' _ (Subgroup.inv_mem _ hgb)]
    exact Subgroup.inv_mem _ hgb

theorem mem_transvN1 {b₀ : G} {K E : Subgroup G} {g : G} :
    g ∈ transvN1 b₀ K E ↔ g ∈ Subgroup.normalizer (E : Set G) ∧
      (∀ a ∈ E ⊓ K, g * a * g⁻¹ = a) ∧ b₀⁻¹ * (g * b₀ * g⁻¹) ∈ E ⊓ K :=
  Iff.rfl

@[expose] def transvBeta (b₀ : G) (K E : Subgroup G) : ↥(transvN1 b₀ K E) →* ↥(E ⊓ K) where
  toFun g := ⟨b₀⁻¹ * ((g : G) * b₀ * (g : G)⁻¹), g.2.2.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by
    show b₀⁻¹ * ((g : G) * h * b₀ * ((g : G) * h)⁻¹) =
      b₀⁻¹ * ((g : G) * b₀ * (g : G)⁻¹) * (b₀⁻¹ * ((h : G) * b₀ * (h : G)⁻¹))
    have h1 := g.2.2.1 _ h.2.2.2
    calc b₀⁻¹ * ((g : G) * h * b₀ * ((g : G) * h)⁻¹) =
        b₀⁻¹ * ((g : G) * b₀ * (g : G)⁻¹) *
          ((g : G) * (b₀⁻¹ * ((h : G) * b₀ * (h : G)⁻¹)) * (g : G)⁻¹) := by group
      _ = _ := by rw [h1])

theorem transvBeta_apply {b₀ : G} {K E : Subgroup G} (g : ↥(transvN1 b₀ K E)) :
    ((transvBeta b₀ K E g : ↥(E ⊓ K)) : G) = b₀⁻¹ * ((g : G) * b₀ * (g : G)⁻¹) :=
  rfl

theorem conj_b0_of_mem_transvN1 {b₀ : G} {K E : Subgroup G} (g : ↥(transvN1 b₀ K E)) :
    (g : G) * b₀ * (g : G)⁻¹ = b₀ * (transvBeta b₀ K E g : G) := by
  rw [transvBeta_apply, mul_inv_cancel_left]

namespace TransvSetup

variable [Finite G] {b₀ : G} {K E : Subgroup G}

theorem b0_mem (h : TransvSetup b₀ K E) : b₀ ∈ E :=
  h.sup ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers b₀)

theorem comm (h : TransvSetup b₀ K E) {x y : G} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x :=
  h.elem.comm hx hy

theorem mem_centralizer_of (h : TransvSetup b₀ K E) {g : G} (hgb : g * b₀ = b₀ * g)
    (hgA : ∀ a ∈ E ⊓ K, g * a = a * g) : g ∈ Subgroup.centralizer (E : Set G) := by
  have hle : E ≤ Subgroup.centralizer ({g} : Set G) := by
    rw [← h.sup]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) fun a ha => ?_
    · exact Subgroup.mem_centralizer_iff.mpr fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hgb
    · exact Subgroup.mem_centralizer_iff.mpr fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hgA a ha
  exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (hle hx) g (Set.mem_singleton g)).symm

theorem centralizer_le (h : TransvSetup b₀ K E) :
    Subgroup.centralizer (E : Set G) ≤ transvN1 b₀ K E := by
  intro g hg
  refine ⟨Subgroup.centralizer_le_normalizer _ hg, fun a ha => ?_, ?_⟩
  · rw [← Subgroup.mem_centralizer_iff.mp hg a ha.1]; group
  · rw [show g * b₀ * g⁻¹ = b₀ by rw [← Subgroup.mem_centralizer_iff.mp hg b₀ h.b0_mem]; group,
      inv_mul_cancel]
    exact Subgroup.one_mem _

theorem le_transvN1 (h : TransvSetup b₀ K E) : E ≤ transvN1 b₀ K E := by
  intro e he
  refine ⟨?_, fun a ha => ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact E.mul_mem (E.mul_mem he hx) (E.inv_mem he)
    · intro hx
      have := E.mul_mem (E.mul_mem (E.inv_mem he) hx) he
      rwa [show e⁻¹ * (e * x * e⁻¹) * e = x by group] at this
  · rw [h.comm he ha.1]; group
  · rw [h.comm he h.b0_mem, mul_inv_cancel_right, inv_mul_cancel]
    exact Subgroup.one_mem _

theorem beta_eq_one_iff (h : TransvSetup b₀ K E) (g : ↥(transvN1 b₀ K E)) :
    transvBeta b₀ K E g = 1 ↔ (g : G) ∈ Subgroup.centralizer (E : Set G) := by
  constructor
  · intro hg
    have h1 : (g : G) * b₀ * (g : G)⁻¹ = b₀ := by
      rw [conj_b0_of_mem_transvN1, hg, OneMemClass.coe_one, mul_one]
    refine h.mem_centralizer_of (by
      calc (g : G) * b₀ = (g : G) * b₀ * (g : G)⁻¹ * g := by group
        _ = b₀ * g := by rw [h1]) fun a ha => ?_
    calc (g : G) * a = (g : G) * a * (g : G)⁻¹ * g := by group
      _ = a * g := by rw [g.2.2.1 a ha]
  · intro hg
    apply Subtype.ext
    rw [transvBeta_apply, show (g : G) * b₀ * (g : G)⁻¹ = b₀ by
      rw [← Subgroup.mem_centralizer_iff.mp hg b₀ h.b0_mem]; group, inv_mul_cancel,
      OneMemClass.coe_one]

theorem beta_surjective (h : TransvSetup b₀ K E) : Function.Surjective (transvBeta b₀ K E) := by
  rintro ⟨β, hβ⟩
  obtain ⟨g, hgN, hgA, hgb⟩ := h.transv β hβ
  refine ⟨⟨g, hgN, hgA, ?_⟩, Subtype.ext ?_⟩
  · rw [hgb, inv_mul_cancel_left]; exact hβ
  · rw [transvBeta_apply]
    show b₀⁻¹ * (g * b₀ * g⁻¹) = β
    rw [hgb, inv_mul_cancel_left]

theorem conj_mem_transvN1 (h : TransvSetup b₀ K E) {n : G}
    (hn : n ∈ Subgroup.normalizer (E : Set G)) {g : G} (hg : g ∈ transvN1 b₀ K E) :
    n * g * n⁻¹ ∈ transvN1 b₀ K E := by
  obtain ⟨hgN, hgA, hgb⟩ := hg
  have hninv : n⁻¹ ∈ Subgroup.normalizer (E : Set G) := Subgroup.inv_mem _ hn
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hgN) hninv, fun a ha => ?_, ?_⟩
  · have ha' : n⁻¹ * a * n ∈ E ⊓ K := by
      have := h.inv n⁻¹ hninv a ha
      rwa [inv_inv] at this
    rw [show n * g * n⁻¹ * a * (n * g * n⁻¹)⁻¹ = n * (g * (n⁻¹ * a * n) * g⁻¹) * n⁻¹ by group,
      hgA _ ha']
    group
  ·
    have hb : n⁻¹ * b₀ * n ∈ E := by
      have := (Subgroup.mem_normalizer_iff.mp hninv b₀).mp h.b0_mem
      rwa [inv_inv] at this
    rw [← h.sup] at hb
    obtain ⟨x, hx, a', ha', hxa⟩ := fs81Sp_mem_sup_of_commute (A := Subgroup.zpowers b₀)
      (B := E ⊓ K) (fun x hx y hy => h.comm (h.sup ▸ Subgroup.mem_sup_left hx) hy.1) hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    set β := b₀⁻¹ * (g * b₀ * g⁻¹) with hβ
    have hgb' : g * b₀ * g⁻¹ = b₀ * β := by rw [hβ, mul_inv_cancel_left]
    have hβb : β * b₀ = b₀ * β := h.comm hgb.1 h.b0_mem
    have hgi : g * b₀ ^ i * g⁻¹ = b₀ ^ i * β ^ i := by
      rw [← conj_zpow, hgb', (Commute.symm hβb).mul_zpow]
    have hkey : n * g * n⁻¹ * b₀ * (n * g * n⁻¹)⁻¹ = b₀ * (n * β ^ i * n⁻¹) := by
      have e1 : b₀ = n * (b₀ ^ i * a') * n⁻¹ := by rw [← hxa]; group
      calc n * g * n⁻¹ * b₀ * (n * g * n⁻¹)⁻¹
          = n * (g * (n⁻¹ * b₀ * n) * g⁻¹) * n⁻¹ := by group
        _ = n * (g * b₀ ^ i * g⁻¹ * (g * a' * g⁻¹)) * n⁻¹ := by rw [hxa]; group
        _ = n * (b₀ ^ i * β ^ i * a') * n⁻¹ := by rw [hgi, hgA a' ha']
        _ = n * (b₀ ^ i * a') * n⁻¹ * (n * β ^ i * n⁻¹) := by
            rw [show b₀ ^ i * β ^ i * a' = b₀ ^ i * a' * β ^ i by
              rw [mul_assoc, mul_assoc, h.comm (Subgroup.zpow_mem _ hgb.1 i) ha'.1]]
            group
        _ = b₀ * (n * β ^ i * n⁻¹) := by rw [← e1]
    rw [hkey, inv_mul_cancel_left]
    exact h.inv n hn _ (Subgroup.zpow_mem _ hgb i)

theorem isPGroup_A (h : TransvSetup b₀ K E) : IsPGroup 3 ↥(E ⊓ K) := fun x =>
  ⟨1, Subtype.ext (by simpa using h.elem.2 _ x.2.1)⟩

theorem card_transvN1 (h : TransvSetup b₀ K E) :
    Nat.card ↥(transvN1 b₀ K E) =
      Nat.card ↥(Subgroup.centralizer (E : Set G)) * Nat.card ↥(E ⊓ K) := by
  rw [← Subgroup.card_ker_mul_card_of_surjective h.beta_surjective]
  congr 1
  have hker : (transvBeta b₀ K E).ker =
      (Subgroup.centralizer (E : Set G)).subgroupOf (transvN1 b₀ K E) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, h.beta_eq_one_iff]
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.centralizer_le).toEquiv]

theorem card_E_eq (h : TransvSetup b₀ K E) :
    Nat.card E = 3 ^ (Nat.card ↥(Subgroup.centralizer (E : Set G))).factorization 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEC : E ≤ Subgroup.centralizer (E : Set G) := fun e he =>
    Subgroup.mem_centralizer_iff.mpr fun x hx => h.comm hx he
  have hE3 : IsPGroup 3 (E.subgroupOf (Subgroup.centralizer (E : Set G))) := fun x =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using h.elem.2 _ (Subgroup.mem_subgroupOf.mp x.2)))⟩
  obtain ⟨T, hET⟩ := hE3.exists_le_sylow
  have hTE : (T : Subgroup ↥(Subgroup.centralizer (E : Set G))) ≤
      E.subgroupOf (Subgroup.centralizer (E : Set G)) := by
    intro t ht
    obtain ⟨k, hk⟩ := T.isPGroup' ⟨t, ht⟩
    exact Subgroup.mem_subgroupOf.mpr (h.syl _ t.2 k (by
      have := congrArg (fun x : ↥T => ((x : ↥(Subgroup.centralizer (E : Set G))) : G)) hk
      simpa using this))
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv, ← le_antisymm hTE hET,
    Sylow.card_eq_multiplicity]

theorem exists_transvP1 (h : TransvSetup b₀ K E) :
    ∃ P₁ : Subgroup G, P₁ ≤ transvN1 b₀ K E ∧ IsPGroup 3 P₁ ∧
      Nat.card P₁ = 3 ^ (Nat.card ↥(transvN1 b₀ K E)).factorization 3 ∧ E ≤ P₁ ∧
      ∀ β ∈ E ⊓ K, ∃ x ∈ P₁, ∃ hx : x ∈ transvN1 b₀ K E,
        ((transvBeta b₀ K E ⟨x, hx⟩ : ↥(E ⊓ K)) : G) = β := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N₁ := transvN1 b₀ K E with hN₁
  have hE3 : IsPGroup 3 (E.subgroupOf N₁) := fun x =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using h.elem.2 _ (Subgroup.mem_subgroupOf.mp x.2)))⟩
  obtain ⟨S, hES⟩ := hE3.exists_le_sylow
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card.mp h.isPGroup_A)
  have hSc : Nat.card ↥(S : Subgroup N₁) = Nat.card E * Nat.card ↥(E ⊓ K) := by
    rw [Sylow.card_eq_multiplicity, h.card_transvN1, Nat.factorization_mul Nat.card_pos.ne'
      Nat.card_pos.ne', Finsupp.add_apply, pow_add, ← h.card_E_eq, ha, Nat.factorization_pow,
      Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_three, smul_eq_mul, mul_one]
  set βS := (transvBeta b₀ K E).comp (S : Subgroup N₁).subtype with hβS
  have hker : Nat.card βS.ker ≤ Nat.card E := by
    let f : βS.ker → E := fun x => ⟨(((x : ↥(S : Subgroup N₁)) : N₁) : G), by
      obtain ⟨k, hk⟩ := S.isPGroup' (x : ↥(S : Subgroup N₁))
      refine h.syl _ ((h.beta_eq_one_iff _).mp x.2) k ?_
      have := congrArg (fun y : ↥(S : Subgroup N₁) => ((y : N₁) : G)) hk
      simpa using this⟩
    have hf : Function.Injective f := by
      intro x y hxy
      have h1 : (((x : ↥(S : Subgroup N₁)) : N₁) : G) = (((y : ↥(S : Subgroup N₁)) : N₁) : G) :=
        congrArg (fun z : ↥E => (z : G)) hxy
      exact Subtype.ext (Subtype.ext (Subtype.ext h1))
    exact Nat.card_le_card_of_injective f hf
  have hrange : βS.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h1 := Subgroup.card_ker_mul_card_range βS
    rw [hSc] at h1
    have h2 : Nat.card ↥(E ⊓ K) ≤ Nat.card βS.range := by
      by_contra hlt
      push Not at hlt
      have := Nat.mul_lt_mul_of_le_of_lt hker hlt Nat.card_pos
      omega
    exact le_antisymm (Subgroup.card_le_card_group _) h2
  refine ⟨(S : Subgroup N₁).map N₁.subtype, Subgroup.map_subtype_le _,
    S.isPGroup'.map _, ?_, fun e he => ?_, fun β hβ => ?_⟩
  · rw [Subgroup.card_map_of_injective N₁.subtype_injective, Sylow.card_eq_multiplicity]
  · exact ⟨⟨e, h.le_transvN1 he⟩, hES (Subgroup.mem_subgroupOf.mpr he), rfl⟩
  · obtain ⟨x, hx⟩ := hrange ▸ (Subgroup.mem_top (⟨β, hβ⟩ : ↥(E ⊓ K)))
    exact ⟨((x : ↥(S : Subgroup N₁)) : N₁), ⟨x, x.2, rfl⟩, (x : N₁).2,
      congrArg Subtype.val hx⟩

theorem mem_E_of_beta_eq_one (h : TransvSetup b₀ K E) {P₁ : Subgroup G} (hP₁ : IsPGroup 3 P₁)
    {x : G} (hxP : x ∈ P₁) (hx : x ∈ transvN1 b₀ K E) (hβ : transvBeta b₀ K E ⟨x, hx⟩ = 1) :
    x ∈ E := by
  obtain ⟨k, hk⟩ := hP₁ ⟨x, hxP⟩
  exact h.syl x ((h.beta_eq_one_iff _).mp hβ) k
    (by simpa using congrArg (fun z : ↥P₁ => (z : G)) hk)

theorem exists_mul_centralizer (h : TransvSetup b₀ K E) {P₁ : Subgroup G}
    (hβP : ∀ β ∈ E ⊓ K, ∃ x ∈ P₁, ∃ hx : x ∈ transvN1 b₀ K E,
        ((transvBeta b₀ K E ⟨x, hx⟩ : ↥(E ⊓ K)) : G) = β)
    {g : G} (hg : g ∈ transvN1 b₀ K E) :
    ∃ p ∈ P₁, ∃ c ∈ Subgroup.centralizer (E : Set G), g = p * c := by
  obtain ⟨p, hp, hpN, hpβ⟩ := hβP _ (transvBeta b₀ K E ⟨g, hg⟩).2
  refine ⟨p, hp, p⁻¹ * g, ?_, by group⟩
  have hmem : p⁻¹ * g ∈ transvN1 b₀ K E := Subgroup.mul_mem _ (Subgroup.inv_mem _ hpN) hg
  have hβ1 : transvBeta b₀ K E ⟨p⁻¹ * g, hmem⟩ = 1 := by
    have e : (⟨p⁻¹ * g, hmem⟩ : ↥(transvN1 b₀ K E)) = (⟨p, hpN⟩ : ↥(transvN1 b₀ K E))⁻¹ * ⟨g, hg⟩ :=
      rfl
    rw [e, map_mul, map_inv, inv_mul_eq_one]
    exact Subtype.ext hpβ
  exact (h.beta_eq_one_iff _).mp hβ1

end TransvSetup

theorem exists_conj_le_of_card_three [Finite G] {H Q D : Subgroup G} (hQH : Q ≤ H)
    (hQ : Nat.card Q = 3 ^ (Nat.card H).factorization 3) (hDH : D ≤ H) (hD : IsPGroup 3 D) :
    ∃ g ∈ H, D.map (MulAut.conj g).toMonoidHom ≤ Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Sylow 3 H := Sylow.ofCard (Q.subgroupOf H) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv, hQ])
  have hD' : IsPGroup 3 (D.subgroupOf H) := hD.of_equiv (Subgroup.subgroupOfEquivOfLe hDH).symm
  obtain ⟨R, hR⟩ := hD'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H R S
  refine ⟨g, g.2, ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  have hdR : (⟨d, hDH hd⟩ : H) ∈ (R : Subgroup H) := hR (Subgroup.mem_subgroupOf.2 hd)
  have hmem : (MulAut.conj g) • (⟨d, hDH hd⟩ : H) ∈ (S : Subgroup H) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hdR
  have hS : (S : Subgroup H) = Q.subgroupOf H := Sylow.coe_ofCard _ _
  rw [hS, Subgroup.mem_subgroupOf] at hmem
  simpa [MulAut.smul_def, MulAut.conj_apply] using hmem

namespace TransvSetup

variable [Finite G] {b₀ : G} {K E : Subgroup G}

theorem exists_centralizer_mul_mem_normalizer (h : TransvSetup b₀ K E) {P₁ : Subgroup G}
    (hP₁N : P₁ ≤ transvN1 b₀ K E) (hP₁ : IsPGroup 3 P₁)
    (hcard : Nat.card P₁ = 3 ^ (Nat.card ↥(transvN1 b₀ K E)).factorization 3)
    (hβP : ∀ β ∈ E ⊓ K, ∃ x ∈ P₁, ∃ hx : x ∈ transvN1 b₀ K E,
        ((transvBeta b₀ K E ⟨x, hx⟩ : ↥(E ⊓ K)) : G) = β)
    {g : G} (hg : g ∈ Subgroup.normalizer (E : Set G)) :
    ∃ c ∈ Subgroup.centralizer (E : Set G), c * g ∈ Subgroup.normalizer (P₁ : Set G) := by
  have hD : P₁.map (MulAut.conj g).toMonoidHom ≤ transvN1 b₀ K E := by
    rintro _ ⟨x, hx, rfl⟩
    exact h.conj_mem_transvN1 hg (hP₁N hx)
  obtain ⟨k, hk, hkle⟩ := exists_conj_le_of_card_three hP₁N hcard hD (hP₁.map _)
  have hkeq : (P₁.map (MulAut.conj g).toMonoidHom).map (MulAut.conj k).toMonoidHom = P₁ := by
    refine Subgroup.eq_of_le_of_card_ge hkle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj k).injective,
      Subgroup.card_map_of_injective (MulAut.conj g).injective]
  obtain ⟨p, hp, c, hc, rfl⟩ := h.exists_mul_centralizer hβP hk
  refine ⟨c, hc, ?_⟩
  have hkg : p * c * g ∈ Subgroup.normalizer (P₁ : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    conv_rhs => rw [← hkeq]
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hp)) hkg
  rwa [show p⁻¹ * (p * c * g) = c * g by group] at this

end TransvSetup

end CFSG.StandardType.FrameRoute.FS81

end
