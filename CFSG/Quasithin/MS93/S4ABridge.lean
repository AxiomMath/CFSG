module

public import CFSG.Quasithin.MS93.S4AL2
public import CFSG.Quasithin.MS93.ML3Stmt
public import CFSG.Quasithin.MS93.S4ASL3

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

section Bar

variable {𝒰 : Type} [Group 𝒰] {K N : Subgroup 𝒰} [(N.subgroupOf K).Normal]

@[expose] noncomputable def barSub (K N : Subgroup 𝒰) [(N.subgroupOf K).Normal]
    (A : Subgroup 𝒰) : Subgroup (↥K ⧸ N.subgroupOf K) :=
  (A.subgroupOf K).map (QuotientGroup.mk' (N.subgroupOf K))

theorem mem_barSub {A : Subgroup 𝒰} {x : ↥K ⧸ N.subgroupOf K} :
    x ∈ barSub K N A ↔ ∃ k : ↥K, (k : 𝒰) ∈ A ∧ QuotientGroup.mk' (N.subgroupOf K) k = x := by
  simp only [barSub, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem mk_mem_barSub {A : Subgroup 𝒰} {k : ↥K} (hk : (k : 𝒰) ∈ A) :
    QuotientGroup.mk' (N.subgroupOf K) k ∈ barSub K N A :=
  mem_barSub.mpr ⟨k, hk, rfl⟩

theorem subgroupOf_commutator {A B : Subgroup 𝒰} (hA : A ≤ K) (hB : B ≤ K) :
    ⁅A, B⁆.subgroupOf K = ⁅A.subgroupOf K, B.subgroupOf K⁆ := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le hB,
    Subgroup.map_subgroupOf_eq_of_le ((Subgroup.commutator_mono hA hB).trans
      (Subgroup.commutator_le_self K))]

theorem barSub_commutator {A B : Subgroup 𝒰} (hA : A ≤ K) (hB : B ≤ K) :
    barSub K N ⁅A, B⁆ = ⁅barSub K N A, barSub K N B⁆ := by
  rw [barSub, subgroupOf_commutator hA hB, Subgroup.map_commutator]
  rfl

theorem barSub_le_barSub_iff {A B : Subgroup 𝒰} (hA : A ≤ K) (hB : B ≤ K) (hN : N ≤ K) :
    barSub K N A ≤ barSub K N B ↔ A ≤ B ⊔ N := by
  rw [barSub, barSub, map_mk_le_map_mk_iff,
    ← Subgroup.map_le_map_iff_of_injective K.subtype_injective, Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hA, Subgroup.map_subgroupOf_eq_of_le hB,
    Subgroup.map_subgroupOf_eq_of_le hN]

theorem barSub_eq_bot_iff {A : Subgroup 𝒰} (hA : A ≤ K) (hN : N ≤ K) :
    barSub K N A = ⊥ ↔ A ≤ N := by
  rw [barSub, map_mk_eq_bot_iff, ← Subgroup.map_le_map_iff_of_injective K.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hA, Subgroup.map_subgroupOf_eq_of_le hN]

theorem barSub_mono {A B : Subgroup 𝒰} (h : A ≤ B) : barSub K N A ≤ barSub K N B :=
  Subgroup.map_mono fun _ hx => h hx

theorem barSub_top : barSub K N K = ⊤ := by
  rw [barSub, Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective _)]

theorem card_barSub_le {A : Subgroup 𝒰} [Finite ↥A] : Nat.card ↥(barSub K N A) ≤ Nat.card ↥A := by
  let e : ↥(A.subgroupOf K) → ↥A := fun x => ⟨((x : ↥K) : 𝒰), x.2⟩
  have he : Function.Injective e := by
    intro x y hxy
    have : (((x : ↥K) : 𝒰)) = ((y : ↥K) : 𝒰) := congrArg (fun z : ↥A => (z : 𝒰)) hxy
    exact Subtype.ext (Subtype.ext this)
  have hfin : Finite ↥(A.subgroupOf K) := Finite.of_injective e he
  calc Nat.card ↥(barSub K N A)
      ≤ Nat.card ↥(A.subgroupOf K) :=
        Nat.card_le_card_of_surjective _
          ((QuotientGroup.mk' (N.subgroupOf K)).subgroupMap_surjective (A.subgroupOf K))
    _ ≤ Nat.card ↥A := Nat.card_le_card_of_injective e he

end Bar

section BarNat

variable {𝒰 : Type} [Group 𝒰] {K N : Subgroup 𝒰} [(N.subgroupOf K).Normal]
  {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
  {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)}

@[expose] noncomputable def barHom (φ : ↥K →* ↥Γ) (hN : ∀ n : ↥K, (n : 𝒰) ∈ N → φ n = 1) :
    ↥(⊤ : Subgroup (↥K ⧸ N.subgroupOf K)) →* ↥Γ :=
  natQuot (φ.comp (Subgroup.topEquiv (G := ↥K)).toMonoidHom) fun n hn => hN n hn

theorem barHom_surjective {φ : ↥K →* ↥Γ} (hN : ∀ n : ↥K, (n : 𝒰) ∈ N → φ n = 1)
    (hφ : Function.Surjective φ) : Function.Surjective (barHom φ hN) := by
  intro y
  obtain ⟨k, rfl⟩ := hφ y
  exact ⟨⟨QuotientGroup.mk' (N.subgroupOf K) k, Subgroup.mem_top _⟩, rfl⟩

theorem isSumOfNaturalModulesVia_top {V Z : Subgroup 𝒰} {φ : ↥K →* ↥Γ} {dual : Bool} {k : ℕ}
    (h : IsSumOfNaturalModulesVia K V Z φ dual k) (hV : V ≤ K) :
    IsSumOfNaturalModulesVia (⊤ : Subgroup ↥K) (V.subgroupOf K) (Z.subgroupOf K)
      (φ.comp (Subgroup.topEquiv (G := ↥K)).toMonoidHom) dual k := by
  have hKV := h.1
  have hZV := h.2.1
  refine isSumOfNaturalModulesVia_of_equiv h (Subgroup.topEquiv (G := ↥K))
    (Subgroup.subgroupOfEquivOfLe hV) ?_ ?_ ?_ ?_
  · intro a _
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have := Subgroup.mem_normalizer_iff.mp (hKV a.2) (x : 𝒰)
    simpa using this
  · intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hZV (Subgroup.mem_subgroupOf.mp hx))
  · intro v
    rfl
  · intro a u v huv
    simpa using congrArg Subtype.val huv

theorem isSumOfNaturalModulesVia_barSub {V Z : Subgroup 𝒰} {φ : ↥K →* ↥Γ} {dual : Bool} {k : ℕ}
    (h : IsSumOfNaturalModulesVia K V Z φ dual k) (hV : V ≤ K)
    (hN : ∀ n : ↥K, (n : 𝒰) ∈ N → φ n = 1) (hVN : V ⊓ N ≤ Z) :
    IsSumOfNaturalModulesVia (⊤ : Subgroup (↥K ⧸ N.subgroupOf K)) (barSub K N V)
      (barSub K N Z) (barHom φ hN) dual k := by
  refine isSumOfNaturalModulesVia_quotient (isSumOfNaturalModulesVia_top h hV) _ ?_
  rintro x ⟨hxV, hxN⟩
  exact Subgroup.mem_subgroupOf.mpr (hVN ⟨Subgroup.mem_subgroupOf.mp hxV,
    Subgroup.mem_subgroupOf.mp hxN⟩)

theorem barSub_bot : barSub K N (⊥ : Subgroup 𝒰) = ⊥ := by
  rw [barSub, Subgroup.bot_subgroupOf, Subgroup.map_bot]

theorem barSub_normal {W : Subgroup 𝒰} (hW : K ≤ Subgroup.normalizer (W : Set 𝒰)) :
    (barSub K N W).Normal := by
  have : (W.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hW
  exact Subgroup.Normal.map this _ (QuotientGroup.mk'_surjective _)

theorem barSub_closure_conj {X : Subgroup 𝒰} (hXK : X ≤ K) :
    barSub K N (Subgroup.closure {u | ∃ k : ↥K, ∃ x ∈ X, (k : 𝒰) * x * (k : 𝒰)⁻¹ = u}) =
      Subgroup.closure {u | ∃ l : ↥(⊤ : Subgroup (↥K ⧸ N.subgroupOf K)), ∃ x ∈ barSub K N X,
        (l : ↥K ⧸ N.subgroupOf K) * x * (l : ↥K ⧸ N.subgroupOf K)⁻¹ = u} := by
  set S : Set 𝒰 := {u | ∃ k : ↥K, ∃ x ∈ X, (k : 𝒰) * x * (k : 𝒰)⁻¹ = u} with hS
  have hSK : Subgroup.closure S ≤ K := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, x, hx, rfl⟩
    exact K.mul_mem (K.mul_mem k.2 (hXK hx)) (K.inv_mem k.2)
  apply le_antisymm
  ·
    have key : ∀ u ∈ Subgroup.closure S, ∃ hu : u ∈ K,
        QuotientGroup.mk' (N.subgroupOf K) ⟨u, hu⟩ ∈ Subgroup.closure {u | ∃ l :
          ↥(⊤ : Subgroup (↥K ⧸ N.subgroupOf K)), ∃ x ∈ barSub K N X,
            (l : ↥K ⧸ N.subgroupOf K) * x * (l : ↥K ⧸ N.subgroupOf K)⁻¹ = u} := by
      intro u hu
      induction hu using Subgroup.closure_induction with
      | mem u hu =>
        obtain ⟨k, x, hx, rfl⟩ := hu
        refine ⟨K.mul_mem (K.mul_mem k.2 (hXK hx)) (K.inv_mem k.2), Subgroup.subset_closure ?_⟩
        refine ⟨⟨QuotientGroup.mk' (N.subgroupOf K) k, Subgroup.mem_top _⟩,
          QuotientGroup.mk' (N.subgroupOf K) ⟨x, hXK hx⟩, mk_mem_barSub hx, ?_⟩
        rw [← map_mul, ← map_inv, ← map_mul]
        rfl
      | one =>
        refine ⟨K.one_mem, ?_⟩
        have : QuotientGroup.mk' (N.subgroupOf K) ⟨1, K.one_mem⟩ = 1 := map_one _
        rw [this]
        exact Subgroup.one_mem _
      | mul u v _ _ hu hv =>
        obtain ⟨hu, hu'⟩ := hu
        obtain ⟨hv, hv'⟩ := hv
        refine ⟨K.mul_mem hu hv, ?_⟩
        have : QuotientGroup.mk' (N.subgroupOf K) ⟨u * v, K.mul_mem hu hv⟩ =
            QuotientGroup.mk' (N.subgroupOf K) ⟨u, hu⟩ *
              QuotientGroup.mk' (N.subgroupOf K) ⟨v, hv⟩ := by
          rw [← map_mul]
          rfl
        rw [this]
        exact Subgroup.mul_mem _ hu' hv'
      | inv u _ hu =>
        obtain ⟨hu, hu'⟩ := hu
        refine ⟨K.inv_mem hu, ?_⟩
        have : QuotientGroup.mk' (N.subgroupOf K) ⟨u⁻¹, K.inv_mem hu⟩ =
            (QuotientGroup.mk' (N.subgroupOf K) ⟨u, hu⟩)⁻¹ := by
          rw [← map_inv]
          rfl
        rw [this]
        exact Subgroup.inv_mem _ hu'
    intro y hy
    obtain ⟨k, hk, rfl⟩ := mem_barSub.mp hy
    obtain ⟨hu, hu'⟩ := key _ hk
    exact hu'
  · rw [Subgroup.closure_le]
    rintro _ ⟨⟨l, -⟩, y, hy, rfl⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf K) l
    obtain ⟨x, hx, rfl⟩ := mem_barSub.mp hy
    have hmem : ((k : 𝒰) * x * (k : 𝒰)⁻¹) ∈ Subgroup.closure S :=
      Subgroup.subset_closure ⟨k, x, hx, rfl⟩
    have := mk_mem_barSub (K := K) (N := N) (k := k * x * k⁻¹) (by simpa using hmem)
    simpa [map_mul, map_inv] using this

end BarNat

section MS17

variable {𝒰 : Type} [Group 𝒰] {K N : Subgroup 𝒰} [(N.subgroupOf K).Normal] [Finite ↥K]

open CFSG.Assembly.LowTwoRank

theorem ms17i_bar (h17 : MS17i) (hNK : N ≤ K) {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hn : Fintype.card F = 2 ^ n) {ψ : ↥K →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hNψ : ∀ x : ↥K, (x : 𝒰) ∈ N → ψ x = 1)
    {Z U C W X : Subgroup 𝒰} (hZK : Z ≤ K) (hUK : U ≤ K) (hWK : W ≤ K)
    (hZ : IsSumOfNaturalModulesVia K Z ⊥ ψ false 1) (hZN : Z ⊓ N = ⊥)
    (hUC : IsSumOfNaturalModulesVia K U C ψ false 1) (hUN : U ⊓ N ≤ C)
    (hZC : Z ≤ C ⊔ N) (hCK : ⁅C, K⁆ ≤ Z ⊔ N) (hWn : K ≤ Subgroup.normalizer (W : Set 𝒰))
    (hZU : ⁅Z, U⁆ ≤ N) (hZW : ⁅Z, W⁆ ≤ N) (hUW : ⁅U, W⁆ ≤ Z ⊔ N) (hXU : X ≤ U)
    (hgen : U = Subgroup.closure {u | ∃ k : ↥K, ∃ x ∈ X, (k : 𝒰) * x * (k : 𝒰)⁻¹ = u})
    (hstab : ∀ k : ↥K, toSL3 ψ k ∈ (ptStab : Subgroup (SL3 F)) →
      ∀ x ∈ X, (k : 𝒰) * x * (k : 𝒰)⁻¹ ∈ X ⊔ N)
    (hlevi : ∀ k : ↥K, toSL3 ψ k ∈ (ptLevi : Subgroup (SL3 F)) →
      ∀ x ∈ X, x⁻¹ * ((k : 𝒰) * x * (k : 𝒰)⁻¹) ∈ C ⊔ N)
    (hne : ¬ ⁅X, W⁆ ≤ N) {S : Subgroup 𝒰} [Finite ↥S] (hSK : S ≤ K) (hXWS : ⁅X, W⁆ ≤ S ⊔ N)
    (hS : Nat.card ↥S ≤ Nat.card F ^ 2) :
    ⁅C, W⁆ ≤ N ∧ ⁅⁅W, K⁆, U⁆ ≤ N ∧
      (∀ w ∈ W, (∀ x ∈ X, ⁅x, w⁆ ∈ N) → ∀ u ∈ U, ⁅u, w⁆ ∈ N) ∧
      (∀ w ∈ W, (∃ u ∈ U, ⁅u, w⁆ ∉ N) → Z ≤ ⁅U, Subgroup.zpowers w⁆ ⊔ N) := by
  set Q := ↥K ⧸ N.subgroupOf K
  set π := QuotientGroup.mk' (N.subgroupOf K) with hπ
  have hCU : C ≤ U := hUC.2.1
  have hCK' : C ≤ K := hCU.trans hUK
  have hXK : X ≤ K := hXU.trans hUK
  have hbot : barSub K N N = ⊥ := (barSub_eq_bot_iff hNK hNK).mpr le_rfl
  have hsupN : ∀ {A : Subgroup 𝒰}, A ≤ K → barSub K N (A ⊔ N) = barSub K N A := by
    intro A hA
    apply le_antisymm
    · exact (barSub_le_barSub_iff (sup_le hA hNK) hA hNK).mpr le_rfl
    · exact barSub_mono le_sup_left
  have hcomm : ∀ {A B : Subgroup 𝒰}, A ≤ K → B ≤ K → ⁅A, B⁆ ≤ K := fun hA hB =>
    (Subgroup.commutator_mono hA hB).trans (Subgroup.commutator_le_self K)
  have hα := barHom_surjective hNψ hψs
  have hZq : IsSumOfNaturalModulesVia (⊤ : Subgroup Q) (barSub K N Z) ⊥ (barHom ψ hNψ) false 1 := by
    have := isSumOfNaturalModulesVia_barSub hZ hZK hNψ (by rw [hZN])
    rwa [barSub_bot] at this
  have hUq := isSumOfNaturalModulesVia_barSub hUC hUK hNψ hUN
  have h1 : barSub K N Z ≤ barSub K N C := (barSub_le_barSub_iff hZK hCK' hNK).mpr hZC
  have h2 : ⁅barSub K N C, (⊤ : Subgroup Q)⁆ ≤ barSub K N Z := by
    rw [← barSub_top, ← barSub_commutator hCK' le_rfl]
    exact (barSub_le_barSub_iff (hcomm hCK' le_rfl) hZK hNK).mpr hCK
  have h3 : (⊤ : Subgroup Q) ≤ Subgroup.normalizer (barSub K N W : Set Q) := by
    have := barSub_normal (N := N) hWn
    exact Subgroup.le_normalizer_of_normal
  have h4 : ⁅barSub K N Z, barSub K N U⁆ = ⊥ := by
    rw [← barSub_commutator hZK hUK]
    exact (barSub_eq_bot_iff (hcomm hZK hUK) hNK).mpr hZU
  have h5 : ⁅barSub K N Z, barSub K N W⁆ = ⊥ := by
    rw [← barSub_commutator hZK hWK]
    exact (barSub_eq_bot_iff (hcomm hZK hWK) hNK).mpr hZW
  have h6 : ⁅barSub K N U, barSub K N W⁆ ≤ barSub K N Z := by
    rw [← barSub_commutator hUK hWK]
    exact (barSub_le_barSub_iff (hcomm hUK hWK) hZK hNK).mpr hUW
  have h7 : barSub K N X ≤ barSub K N U := barSub_mono hXU
  have h8 : barSub K N U = Subgroup.closure {u | ∃ l : ↥(⊤ : Subgroup Q), ∃ x ∈ barSub K N X,
      (l : Q) * x * (l : Q)⁻¹ = u} := by
    rw [hgen]
    exact barSub_closure_conj hXK
  have h9 : ∀ l : ↥(⊤ : Subgroup Q), toSL3 (barHom ψ hNψ) l ∈ (ptStab : Subgroup (SL3 F)) →
      ∀ x ∈ barSub K N X, (l : Q) * x * (l : Q)⁻¹ ∈ barSub K N X := by
    intro l hl x hx
    obtain ⟨k, hk'⟩ := QuotientGroup.mk'_surjective (N.subgroupOf K) (l : Q)
    have hl' : l = ⟨QuotientGroup.mk' (N.subgroupOf K) k, Subgroup.mem_top _⟩ :=
      Subtype.ext hk'.symm
    subst hl'
    obtain ⟨y, hy, rfl⟩ := mem_barSub.mp hx
    have hk : toSL3 ψ k ∈ (ptStab : Subgroup (SL3 F)) := hl
    have hmem := hstab k hk y hy
    rw [← hsupN hXK]
    have := mk_mem_barSub (K := K) (N := N) (k := k * y * k⁻¹) (by simpa using hmem)
    simpa [map_mul, map_inv] using this
  have h10 : ∀ l : ↥(⊤ : Subgroup Q), toSL3 (barHom ψ hNψ) l ∈ (ptLevi : Subgroup (SL3 F)) →
      ∀ x ∈ barSub K N X, x⁻¹ * ((l : Q) * x * (l : Q)⁻¹) ∈ barSub K N C := by
    intro l hl x hx
    obtain ⟨k, hk'⟩ := QuotientGroup.mk'_surjective (N.subgroupOf K) (l : Q)
    have hl' : l = ⟨QuotientGroup.mk' (N.subgroupOf K) k, Subgroup.mem_top _⟩ :=
      Subtype.ext hk'.symm
    subst hl'
    obtain ⟨y, hy, rfl⟩ := mem_barSub.mp hx
    have hk : toSL3 ψ k ∈ (ptLevi : Subgroup (SL3 F)) := hl
    have hmem := hlevi k hk y hy
    rw [← hsupN hCK']
    have := mk_mem_barSub (K := K) (N := N) (k := y⁻¹ * (k * y * k⁻¹)) (by simpa using hmem)
    simpa [map_mul, map_inv] using this
  have h11 : ⁅barSub K N X, barSub K N W⁆ ≠ ⊥ := by
    rw [← barSub_commutator hXK hWK, Ne, barSub_eq_bot_iff (hcomm hXK hWK) hNK]
    exact hne
  have h12 : Nat.card ↥⁅barSub K N X, barSub K N W⁆ ≤ Nat.card F ^ 2 := by
    rw [← barSub_commutator hXK hWK]
    have hle : barSub K N ⁅X, W⁆ ≤ barSub K N S := by
      rw [← hsupN hSK]
      exact barSub_mono hXWS
    have hfin : Finite ↥(barSub K N S) := by
      have : Finite Q := inferInstance
      infer_instance
    exact (Subgroup.card_le_of_le hle).trans (card_barSub_le.trans hS)
  obtain ⟨c1, c2, -, c4, c5⟩ := h17 Q F n hn ⊤ (barSub K N Z) (barSub K N W) (barSub K N U)
    (barSub K N C) (barSub K N X) (barHom ψ hNψ) hα hZq hUq h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  have hker : ∀ k : ↥K, π k = 1 ↔ (k : 𝒰) ∈ N := by
    intro k
    rw [← MonoidHom.mem_ker, hπ, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
  have hcommQ : ∀ a b : ↥K, π a * π b = π b * π a ↔ ⁅(a : 𝒰), (b : 𝒰)⁆ ∈ N := by
    intro a b
    have e : (⁅(a : 𝒰), (b : 𝒰)⁆ : 𝒰) = ((⁅a, b⁆ : ↥K) : 𝒰) := rfl
    rw [e, ← hker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← barSub_commutator hCK' hWK] at c1
    exact (barSub_eq_bot_iff (hcomm hCK' hWK) hNK).mp c1
  · rw [← barSub_top, ← barSub_commutator hWK le_rfl,
      ← barSub_commutator (hcomm hWK le_rfl) hUK] at c2
    exact (barSub_eq_bot_iff (hcomm (hcomm hWK le_rfl) hUK) hNK).mp c2
  · intro w hw hXw u hu
    have hwc : π ⟨w, hWK hw⟩ ∈ Subgroup.centralizer (barSub K N X : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := mem_barSub.mp hy
      exact (hcommQ x ⟨w, hWK hw⟩).mpr (hXw x hx)
    have hwq : π ⟨w, hWK hw⟩ ∈ barSub K N W ⊓ Subgroup.centralizer (barSub K N X : Set Q) :=
      Subgroup.mem_inf.mpr ⟨mk_mem_barSub hw, hwc⟩
    rw [c4] at hwq
    have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hwq).2 (π ⟨u, hUK hu⟩)
      (mk_mem_barSub hu)
    exact (hcommQ ⟨u, hUK hu⟩ ⟨w, hWK hw⟩).mp this
  · rintro w hw ⟨u, hu, huw⟩
    have hnc : π ⟨w, hWK hw⟩ ∉ Subgroup.centralizer (barSub K N U : Set Q) := by
      intro hc
      apply huw
      exact (hcommQ ⟨u, hUK hu⟩ ⟨w, hWK hw⟩).mp
        (Subgroup.mem_centralizer_iff.mp hc (π ⟨u, hUK hu⟩) (mk_mem_barSub hu))
    have hz := c5 _ (mk_mem_barSub hw) hnc
    have hzp : Subgroup.zpowers (π ⟨w, hWK hw⟩) = barSub K N (Subgroup.zpowers w) := by
      have hsub : (Subgroup.zpowers w).subgroupOf K = Subgroup.zpowers ⟨w, hWK hw⟩ := by
        apply Subgroup.map_injective K.subtype_injective
        rw [Subgroup.map_subgroupOf_eq_of_le
          ((Subgroup.zpowers_le (G := 𝒰) (H := K)).mpr (hWK hw)), MonoidHom.map_zpowers]
        rfl
      rw [barSub, hsub, MonoidHom.map_zpowers]
    have hzK : Subgroup.zpowers w ≤ K := (Subgroup.zpowers_le (G := 𝒰) (H := K)).mpr (hWK hw)
    rw [hzp, ← barSub_commutator hUK hzK] at hz
    exact (barSub_le_barSub_iff hZK (hcomm hUK hzK) hNK).mp hz.ge

end MS17

end CFSG.Quasithin.MS93.S4A
