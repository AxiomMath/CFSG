module

public import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.Adapters.StatedPSLTwo
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.C48

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem isSimpleGroup_psl_two {X : Type} [Group X] {p e : ℕ} (hX : IsPSL 2 p e X) :
    IsSimpleGroup X :=
  CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel_psl_two hX

theorem card_psl_two_two {n : ℕ} {X : Type} [Group X] (h : IsPSL 2 2 n X) :
    Nat.card X = 2 ^ n * (4 ^ n - 1) := by
  obtain ⟨⟨-, hf, -, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 2), hK]
  have hgcd : Nat.gcd 2 (2 ^ n - 1) = 1 := by
    have hodd : Odd (2 ^ n - 1) := by
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have h2 : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
      obtain ⟨m, hm⟩ := h2
      exact ⟨m - 1, by omega⟩
    exact Nat.coprime_two_left.mpr hodd
  have h4 : (2 ^ n) ^ 2 = 4 ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [hgcd, Nat.div_one]
  simp [h4]

theorem card_statedSL_two {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Nat.card ↥(StatedSL 2 F) = 2 ^ n * (4 ^ n - 1) := by
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv]
  have := Fintype.ofFinite F
  rw [Matrix.card_SL_field, Fin.prod_univ_two]
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one]
  rw [← Nat.card_eq_fintype_card, hF]
  have h4 : (2 ^ n) ^ 2 = 4 ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hq : 1 < 2 ^ n := hF ▸ Finite.one_lt_card
  have h2 : 4 ^ n - 2 ^ n = 2 ^ n * (2 ^ n - 1) := by
    rw [Nat.mul_sub_one, ← sq, h4]
  rw [h4, h2, ← mul_assoc, Nat.mul_div_cancel _ (by omega : 0 < 2 ^ n - 1), mul_comm]

theorem eq_one_of_perfect {G : Type} [Group G] {L : Subgroup G} (hperf : ⁅L, L⁆ = L)
    {A : Type} [CommGroup A] (f : ↥L →* A) (a : ↥L) : f a = 1 := by
  have hle : ⁅L, L⁆ ≤ f.ker.map L.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    refine ⟨⁅(⟨x, hx⟩ : ↥L), ⟨y, hy⟩⁆, ?_, rfl⟩
    change ⁅(⟨x, hx⟩ : ↥L), ⟨y, hy⟩⁆ ∈ f.ker
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm,
      mul_comm]
  have ha : (a : G) ∈ f.ker.map L.subtype := hle (hperf.symm ▸ a.2)
  obtain ⟨b, hb, hba⟩ := ha
  rw [← Subtype.ext hba]
  exact hb

section Line

variable {G : Type} [Group G]

theorem isNaturalSection_of_line {K U V Z L : Subgroup G} {ι : Type} [Fintype ι]
    [DecidableEq ι] {F : Type} [Field F] [Finite F] {Γ : Subgroup (GL ι F)}
    (α : ↥K →* ↥Γ) (β : ↥U →* Multiplicative (ι → F)) (hβ : Function.Surjective β)
    (hβker : β.ker = Z.subgroupOf U)
    (hβeq : ∀ (a : ↥K) (u v : ↥U), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) =
        ((α a : GL ι F) : Matrix ι ι F).mulVec (Multiplicative.toAdd (β u)))
    (hline : IsFLineVia U V β) (hLK : L ≤ K) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hperf : ⁅L, L⁆ = L) {n : ℕ} (hF : Nat.card F = 2 ^ n) (hpsl : IsPSL 2 2 n (ModO2 L))
    (hO : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G)) (hnt : ¬ ⁅V, L⁆ ≤ Z) :
    IsNaturalSection L V Z (CFSG.pCore 2 ↥L) (StatedSL 2 F) := by
  classical
  obtain ⟨hVU, W₀, hW₀, hmem⟩ := hline
  let b : Module.Basis (Fin 2) F ↥W₀ := Module.finBasisOfFinrankEq F ↥W₀ hW₀
  have hW : ∀ v : ↥V, Multiplicative.toAdd (β ⟨v, hVU v.2⟩) ∈ W₀ :=
    fun v => (hmem ⟨v, hVU v.2⟩).mp v.2
  let c : ↥V → (Fin 2 → F) := fun v => b.equivFun ⟨_, hW v⟩
  have hc1 : c 1 = 0 := by
    have h0 : (⟨_, hW 1⟩ : ↥W₀) = 0 := by
      apply Subtype.ext
      show Multiplicative.toAdd (β 1) = 0
      rw [map_one]
      rfl
    simp only [c, h0, map_zero]
  have hcmul : ∀ v w : ↥V, c (v * w) = c v + c w := by
    intro v w
    have h0 : (⟨_, hW (v * w)⟩ : ↥W₀) = ⟨_, hW v⟩ + ⟨_, hW w⟩ := by
      apply Subtype.ext
      show Multiplicative.toAdd (β (⟨v, hVU v.2⟩ * ⟨w, hVU w.2⟩)) = _
      rw [map_mul, toAdd_mul]
      rfl
    simp only [c, h0, map_add]
  let β' : ↥V →* Multiplicative (Fin 2 → F) :=
    { toFun := fun v => Multiplicative.ofAdd (c v)
      map_one' := by simp only [hc1, ofAdd_zero]
      map_mul' := fun v w => by simp only [hcmul, ofAdd_add] }
  have hcinj : ∀ v : ↥V, c v = 0 ↔ (v : G) ∈ Z := by
    intro v
    have h1 : c v = 0 ↔ Multiplicative.toAdd (β ⟨v, hVU v.2⟩) = 0 := by
      constructor
      · intro h
        have h2 : (⟨_, hW v⟩ : ↥W₀) = 0 := b.equivFun.injective (by rw [map_zero]; exact h)
        exact congrArg Subtype.val h2
      · intro h
        have h2 : (⟨_, hW v⟩ : ↥W₀) = 0 := Subtype.ext h
        simp only [c, h2, map_zero]
    rw [h1]
    have h3 := MonoidHom.mem_ker (f := β) (x := ⟨v, hVU v.2⟩)
    rw [hβker, Subgroup.mem_subgroupOf] at h3
    exact h3.symm.trans (by rfl)
  let A : ↥L → Matrix ι ι F := fun a => ((α ⟨a, hLK a.2⟩ : GL ι F) : Matrix ι ι F)
  have hconj : ∀ (a : ↥L) (u : G), u ∈ V → (a : G) * u * (a : G)⁻¹ ∈ V := fun a u hu =>
    (Subgroup.mem_normalizer_iff.mp (hLV a.2) u).mp hu
  have hAeq : ∀ (a : ↥L) (u : ↥V), Multiplicative.toAdd (β ⟨_, hVU (hconj a u u.2)⟩) =
      (A a).mulVec (Multiplicative.toAdd (β ⟨u, hVU u.2⟩)) :=
    fun a u => hβeq ⟨a, hLK a.2⟩ ⟨u, hVU u.2⟩ ⟨_, hVU (hconj a u u.2)⟩ rfl
  have hsurjW : ∀ w ∈ W₀, ∃ u : ↥V, Multiplicative.toAdd (β ⟨u, hVU u.2⟩) = w := by
    intro w hw
    obtain ⟨u, hu⟩ := hβ (Multiplicative.ofAdd w)
    have huV : (u : G) ∈ V := (hmem u).mpr (by rw [hu]; exact hw)
    exact ⟨⟨u, huV⟩, by rw [show (⟨(u : G), hVU huV⟩ : ↥U) = u from rfl, hu]; rfl⟩
  have hAW : ∀ a : ↥L, ∀ w ∈ W₀, Matrix.toLin' (A a) w ∈ W₀ := by
    intro a w hw
    obtain ⟨u, rfl⟩ := hsurjW w hw
    rw [Matrix.toLin'_apply, ← hAeq a u]
    exact hW ⟨_, hconj a u u.2⟩
  let f : ↥L → (↥W₀ →ₗ[F] ↥W₀) := fun a => (Matrix.toLin' (A a)).restrict (hAW a)
  have hA1 : A 1 = 1 := by
    show ((α ⟨(1 : G), hLK (1 : ↥L).2⟩ : GL ι F) : Matrix ι ι F) = 1
    rw [show (⟨(1 : G), hLK (1 : ↥L).2⟩ : ↥K) = 1 from rfl, map_one]
    rfl
  have hAmul : ∀ a a' : ↥L, A (a * a') = A a * A a' := by
    intro a a'
    show ((α ⟨(a : G) * a', hLK (a * a').2⟩ : GL ι F) : Matrix ι ι F) = _
    rw [show (⟨(a : G) * a', hLK (a * a').2⟩ : ↥K) = ⟨a, hLK a.2⟩ * ⟨a', hLK a'.2⟩ from rfl,
      map_mul]
    rfl
  have hf1 : f 1 = LinearMap.id := by
    ext w
    simp [f, hA1]
  have hfmul : ∀ a a' : ↥L, f (a * a') = f a ∘ₗ f a' := by
    intro a a'
    ext w
    simp [f, hAmul, Matrix.mulVec_mulVec]
  let M : ↥L →* Matrix (Fin 2) (Fin 2) F :=
    { toFun := fun a => LinearMap.toMatrix b b (f a)
      map_one' := by simp only [hf1, LinearMap.toMatrix_id]
      map_mul' := fun a a' => by
        show LinearMap.toMatrix b b (f (a * a')) = _
        rw [hfmul]
        exact LinearMap.toMatrix_comp b b b _ _ }
  let U2 : ↥L →* GL (Fin 2) F := M.toHomUnits
  have hdet : ∀ a : ↥L, ((U2 a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    intro a
    have h := congrArg Units.val (eq_one_of_perfect hperf
      ((Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).comp U2) a)
    simpa using h
  let α' : ↥L →* ↥(StatedSL 2 F) :=
    U2.codRestrict (StatedSL 2 F) fun a => Subgroup.subset_closure (hdet a)
  have hα'M : ∀ a : ↥L, (((α' a : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) =
      LinearMap.toMatrix b b (f a) := fun a => rfl
  have hβ'eq : ∀ (a : ↥L) (u v : ↥V), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (β' v) =
        ((α' a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
          (Multiplicative.toAdd (β' u)) := by
    intro a u v huv
    have hv : (⟨_, hW v⟩ : ↥W₀) = f a ⟨_, hW u⟩ := by
      apply Subtype.ext
      have h1 := hAeq a u
      rw [show (⟨(a : G) * u * (a : G)⁻¹, hVU (hconj a u u.2)⟩ : ↥U) = ⟨v, hVU v.2⟩ from
        Subtype.ext huv.symm] at h1
      show Multiplicative.toAdd (β ⟨v, hVU v.2⟩) = Matrix.toLin' (A a) _
      rw [h1, Matrix.toLin'_apply]
      rfl
    show c v = _
    rw [hα'M]
    show b.equivFun ⟨_, hW v⟩ = _
    have hrep := LinearMap.toMatrix_mulVec_repr b b (f a) ⟨_, hW u⟩
    rw [hv, Module.Basis.equivFun_apply, ← hrep]
    rfl
  have hker1 : ∀ a : ↥L, (∀ u ∈ V, (a : G) * u * (a : G)⁻¹ = u) → a ∈ α'.ker := by
    intro a ha
    have hfa : f a = LinearMap.id := by
      apply LinearMap.ext
      rintro ⟨w, hw⟩
      obtain ⟨u, rfl⟩ := hsurjW w hw
      apply Subtype.ext
      show (A a).mulVec (Multiplicative.toAdd (β ⟨u, hVU u.2⟩)) =
        Multiplicative.toAdd (β ⟨u, hVU u.2⟩)
      rw [← hAeq a u,
        show (⟨_, hVU (hconj a u u.2)⟩ : ↥U) = ⟨u, hVU u.2⟩ from Subtype.ext (ha u u.2)]
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    apply Units.ext
    show LinearMap.toMatrix b b (f a) = 1
    rw [hfa, LinearMap.toMatrix_id]
  have hOker : CFSG.pCore 2 ↥L ≤ α'.ker := by
    intro x hx
    have hxO : (x : G) ∈ pCoreOf 2 L := by
      rw [pCoreOf]
      exact ⟨x, hx, rfl⟩
    refine hker1 x fun u hu => ?_
    have h := Subgroup.mem_centralizer_iff.mp (hO hxO) u hu
    rw [← h, mul_inv_cancel_right]
  have hkerle : α'.ker ≤ CFSG.pCore 2 ↥L := by
    have hsimp := isSimpleGroup_psl_two hpsl
    have hN : ((α'.ker).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).Normal :=
      (α'.normal_ker).map _ (QuotientGroup.mk'_surjective _)
    have := hN
    rcases hsimp.eq_bot_or_eq_top_of_normal
        ((α'.ker).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) with h | h
    · intro x hx
      have : QuotientGroup.mk' (CFSG.pCore 2 ↥L) x = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact ⟨x, hx, rfl⟩
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    · exfalso
      have hall : ∀ a : ↥L, a ∈ α'.ker := by
        intro a
        have ha : QuotientGroup.mk' (CFSG.pCore 2 ↥L) a ∈
            (α'.ker).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
          rw [h]
          trivial
        obtain ⟨x, hx, hxa⟩ := ha
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxa
        have e : a = x * (x⁻¹ * a) := by group
        rw [e]
        exact mul_mem hx (hOker hxa)
      apply hnt
      rw [Subgroup.commutator_le]
      intro v hv a ha
      set u : ↥V := ⟨v, hv⟩
      set u' : ↥V := ⟨_, hconj ⟨a, ha⟩ v hv⟩
      have h1 := hβ'eq ⟨a, ha⟩ u u' rfl
      have h2 : α' ⟨a, ha⟩ = 1 := hall ⟨a, ha⟩
      rw [h2] at h1
      have h3 : β' u' = β' u := by
        apply Multiplicative.toAdd.injective
        rw [h1]
        exact Matrix.one_mulVec _
      have h4 : c (u * u'⁻¹) = 0 := by
        have : β' (u * u'⁻¹) = 1 := by rw [map_mul, map_inv, h3, mul_inv_cancel]
        exact congrArg Multiplicative.toAdd this
      have h5 := (hcinj _).mp h4
      have e : ⁅v, a⁆ = ((u * u'⁻¹ : ↥V) : G) := by
        simp only [u, u', Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      rw [e]
      exact h5
  have hker : α'.ker = CFSG.pCore 2 ↥L := le_antisymm hkerle hOker
  have hsurj : Function.Surjective α' := by
    rw [← MonoidHom.range_eq_top]
    apply Subgroup.eq_top_of_card_eq
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange α').toEquiv,
      card_statedSL_two hF]
    have h := card_psl_two_two hpsl
    rw [← h]
    exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv
  refine ⟨hLV, α', hsurj, hker, β', ?_, ?_, hβ'eq⟩
  · intro y
    obtain ⟨u, hu⟩ := hsurjW _ (b.equivFun.symm (Multiplicative.toAdd y)).2
    refine ⟨u, ?_⟩
    apply Multiplicative.toAdd.injective
    show c u = _
    have : (⟨_, hW u⟩ : ↥W₀) = b.equivFun.symm (Multiplicative.toAdd y) := Subtype.ext hu
    simp only [c, this, LinearEquiv.apply_symm_apply]
  · ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hcinj]
    exact ⟨fun h => congrArg Multiplicative.toAdd h, fun h => congrArg Multiplicative.ofAdd h⟩

end Line

end CFSG.Quasithin.C48
