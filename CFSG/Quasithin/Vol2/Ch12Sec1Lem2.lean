module

public import CFSG.Quasithin.Vol2.Ch12Sec1Q
public import CFSG.Quasithin.Background.G64Realize
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

namespace Sec1212

section Count

theorem two_mul_card_filter_eq_zero {H : Type*} [Group H] [Fintype H] [DecidableEq H]
    (f : H → ZMod 2) (hf : ∀ x y, f (x * y) = f x + f y) {x₀ : H} (hx₀ : f x₀ ≠ 0) :
    2 * (Finset.univ.filter fun x => f x = 0).card = Fintype.card H := by
  have h01 : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  have h1 : f 1 = 0 := by
    have := hf 1 1
    rw [mul_one] at this
    simpa using this
  have hx₀' := h01 _ hx₀
  have hinv : f x₀⁻¹ = 1 := by
    have h2 := hf x₀ x₀⁻¹
    rw [mul_inv_cancel, h1, hx₀'] at h2
    have key : ∀ y : ZMod 2, 0 = 1 + y → y = 1 := by decide
    exact key _ h2
  have hbij : (Finset.univ.filter fun x => ¬ f x = 0) =
      (Finset.univ.filter fun x => f x = 0).map (mulLeftEmbedding x₀) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      mulLeftEmbedding_apply]
    constructor
    · intro hy
      refine ⟨x₀⁻¹ * y, ?_, by group⟩
      rw [hf, hinv, h01 _ hy]
      decide
    · rintro ⟨x, hx, rfl⟩
      rw [hf, hx, add_zero]
      exact hx₀
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun x => f x = 0)
  rw [hbij, Finset.card_map, Finset.card_univ] at h
  omega

theorem card_mul_card_radical {X Y : Type*} [Group X] [Group Y] [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (β : X → Y → ZMod 2)
    (h₁ : ∀ a b c, β (a * b) c = β a c + β b c) (h₂ : ∀ a c d, β a (c * d) = β a c + β a d) :
    Fintype.card Y * (Finset.univ.filter fun a => ∀ c, β a c = 0).card =
      Fintype.card X * (Finset.univ.filter fun c => ∀ a, β a c = 0).card := by
  have hX : ∀ a, 2 * (Finset.univ.filter fun c => β a c = 0).card =
      Fintype.card Y + if ∀ c, β a c = 0 then Fintype.card Y else 0 := by
    intro a
    split_ifs with ha
    · rw [Finset.filter_true_of_mem fun c _ => ha c, Finset.card_univ]
      ring
    · obtain ⟨c₀, hc₀⟩ := not_forall.mp ha
      rw [two_mul_card_filter_eq_zero (β a) (h₂ a) hc₀, add_zero]
  have hY : ∀ c, 2 * (Finset.univ.filter fun a => β a c = 0).card =
      Fintype.card X + if ∀ a, β a c = 0 then Fintype.card X else 0 := by
    intro c
    split_ifs with hc
    · rw [Finset.filter_true_of_mem fun a _ => hc a, Finset.card_univ]
      ring
    · obtain ⟨a₀, ha₀⟩ := not_forall.mp hc
      rw [two_mul_card_filter_eq_zero (fun a => β a c) (fun a b => h₁ a b c) ha₀, add_zero]
  have hST : ∑ a, (Finset.univ.filter fun c => β a c = 0).card =
      ∑ c, (Finset.univ.filter fun a => β a c = 0).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hS : ∑ a, 2 * (Finset.univ.filter fun c => β a c = 0).card =
      Fintype.card X * Fintype.card Y +
        Fintype.card Y * (Finset.univ.filter fun a => ∀ c, β a c = 0).card := by
    rw [Finset.sum_congr rfl fun a _ => hX a, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
      smul_eq_mul, add_zero, mul_comm (Finset.card _)]
  have hT : ∑ c, 2 * (Finset.univ.filter fun a => β a c = 0).card =
      Fintype.card Y * Fintype.card X +
        Fintype.card X * (Finset.univ.filter fun c => ∀ a, β a c = 0).card := by
    rw [Finset.sum_congr rfl fun c _ => hY c, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
      smul_eq_mul, add_zero, mul_comm (Finset.card _)]
  have h := congrArg (2 * ·) hST
  simp only [Finset.mul_sum] at h
  rw [hS, hT, mul_comm (Fintype.card Y) (Fintype.card X)] at h
  exact Nat.add_left_cancel h

end Count

section Basic

variable {G : Type} [Group G]

theorem decomp_unique {V₁ V₂ : Subgroup G} (hinf : V₁ ⊓ V₂ = ⊥) {a b c d : G} (ha : a ∈ V₁)
    (hb : b ∈ V₂) (hc : c ∈ V₁) (hd : d ∈ V₂) (h : a * b = c * d) : a = c ∧ b = d := by
  have h1 : c⁻¹ * a = d * b⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
  have h2 : c⁻¹ * a ∈ V₁ ⊓ V₂ :=
    ⟨V₁.mul_mem (V₁.inv_mem hc) ha, h1 ▸ V₂.mul_mem hd (V₂.inv_mem hb)⟩
  rw [hinf, Subgroup.mem_bot] at h2
  have h3 : a = c := (inv_mul_eq_one.mp h2).symm
  subst h3
  exact ⟨rfl, mul_left_cancel h⟩

theorem mem_centralizer_iff_conj {X : Subgroup G} {g : G} :
    g ∈ Subgroup.centralizer (X : Set G) ↔ ∀ x ∈ X, g * x * g⁻¹ = x := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    rw [← h x hx, mul_inv_cancel_right]
  · intro h x hx
    calc x * g = (g * x * g⁻¹) * g := by rw [h x hx]
      _ = g * x := by group

theorem mem_centralizer_singleton_iff_conj {g v : G} :
    v ∈ Subgroup.centralizer ({g} : Set G) ↔ g * v * g⁻¹ = v := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    rw [← h, mul_inv_cancel_right]
  · intro h
    calc v * g = (g * v * g⁻¹) * g := by rw [h]
      _ = g * v := by group

theorem exists_ker {X : Subgroup G} [Finite X] (f : G → ZMod 2)
    (hf : ∀ a ∈ X, ∀ b ∈ X, f (a * b) = f a + f b) :
    ∃ K : Subgroup G, K ≤ X ∧ (∀ a ∈ X, a ∈ K ↔ f a = 0) ∧
      ∀ x₀ ∈ X, f x₀ ≠ 0 → 2 * Nat.card K = Nat.card X := by
  classical
  have h1 : f 1 = 0 := by
    have := hf 1 X.one_mem 1 X.one_mem
    rw [mul_one] at this
    simpa using this
  have hinv : ∀ a ∈ X, f a⁻¹ = f a := by
    intro a ha
    have h2 := hf a ha a⁻¹ (X.inv_mem ha)
    rw [mul_inv_cancel, h1] at h2
    have key : ∀ y z : ZMod 2, 0 = y + z → z = y := by decide
    exact key _ _ h2
  let K : Subgroup G :=
    { carrier := {a | a ∈ X ∧ f a = 0}
      mul_mem' := fun {a b} ha hb =>
        ⟨X.mul_mem ha.1 hb.1, by rw [hf a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
      one_mem' := ⟨X.one_mem, h1⟩
      inv_mem' := fun {a} ha => ⟨X.inv_mem ha.1, by rw [hinv a ha.1, ha.2]⟩ }
  refine ⟨K, fun a ha => ha.1, fun a ha => ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩,
    fun x₀ hx₀ hfx₀ => ?_⟩
  have := Fintype.ofFinite ↥X
  have h2 := two_mul_card_filter_eq_zero (fun a : ↥X => f a) (fun a b => hf a a.2 b b.2)
    (x₀ := ⟨x₀, hx₀⟩) hfx₀
  have h3 : Nat.card {a : ↥X // f a = 0} = (Finset.univ.filter fun a : ↥X => f a = 0).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h4 : Nat.card K = Nat.card {a : ↥X // f a = 0} := Nat.card_congr
    { toFun := fun a => ⟨⟨a, a.2.1⟩, a.2.2⟩
      invFun := fun a => ⟨a.1, a.1.2, a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [h4, h3, h2, Nat.card_eq_fintype_card]

end Basic

section Singular

variable {G : Type} [Group G] [Finite G]

theorem card_le_of_forall_singular {L V V₁ V₂ U : Subgroup G} [IsMulCommutative ↥V]
    {β : G → G → ZMod 2} (hV₁ : V₁ ≤ V) (hV₂ : V₂ ≤ V) (hsum : V₁ ⊔ V₂ = V)
    (hinf : V₁ ⊓ V₂ = ⊥) (hβ : IsDualPairing121 L V₁ V₂ β) (hUV : U ≤ V)
    (hU : ∀ u ∈ U, IsSingular121 V₁ V₂ β u) : Nat.card U ≤ Nat.card V₂ := by
  classical
  have := Fintype.ofFinite ↥U
  have := Fintype.ofFinite ↥V₂
  obtain ⟨hβ₁, hβ₂, hnd₁, -, -⟩ := hβ
  have hinf' := InternalSec.inf_subgroupOf_eq_bot (V := V) hinf
  have hsup' := InternalSec.sup_subgroupOf_eq_top hV₁ hV₂ hsum
  set π₁ : ↥U →* ↥V := (H.Pair.proj hinf' hsup').comp (Subgroup.inclusion hUV) with hπ₁def
  have hπ₁ : ∀ u : ↥U, ((π₁ u : ↥V) : G) ∈ V₁ := fun u =>
    Subgroup.mem_subgroupOf.mp (H.Pair.proj_mem hinf' hsup' _)
  have hπ₂ : ∀ u : ↥U, ((π₁ u : ↥V) : G)⁻¹ * u ∈ V₂ := by
    intro u
    obtain ⟨a, ha, b, hb, hab⟩ := H.Pair.exists_decomp hsup' (Subgroup.inclusion hUV u)
    have hpa : π₁ u = a := H.Pair.proj_spec hinf' hsup' ha hb hab
    have hab' : ((a : ↥V) : G) * b = u := congrArg Subtype.val hab
    rw [hpa, ← hab', inv_mul_cancel_left]
    exact Subgroup.mem_subgroupOf.mp hb
  have hπa : ∀ (u : ↥U) {a c : G}, a ∈ V₁ → c ∈ V₂ → (u : G) = a * c →
      ((π₁ u : ↥V) : G) = a := by
    intro u a c ha hc hu
    have h := H.Pair.proj_spec hinf' hsup' (v := Subgroup.inclusion hUV u) (a := ⟨a, hV₁ ha⟩)
      (b := ⟨c, hV₂ hc⟩) (Subgroup.mem_subgroupOf.mpr ha) (Subgroup.mem_subgroupOf.mpr hc)
      (Subtype.ext hu.symm)
    exact congrArg Subtype.val h
  have h0 : ∀ a ∈ V₁, β a 1 = 0 := fun a ha => by
    have := hβ₂ a ha 1 V₂.one_mem 1 V₂.one_mem
    rw [mul_one] at this
    simpa using this
  set β' : ↥U → ↥V₂ → ZMod 2 := fun u c => β (π₁ u : G) c with hβ'
  have h₁ : ∀ a b c, β' (a * b) c = β' a c + β' b c := fun a b c => by
    simp only [hβ', map_mul, Subgroup.coe_mul]
    exact hβ₁ _ (hπ₁ a) _ (hπ₁ b) _ c.2
  have h₂ : ∀ a c d, β' a (c * d) = β' a c + β' a d := fun a c d =>
    hβ₂ _ (hπ₁ a) _ c.2 _ d.2
  have hcount := card_mul_card_radical β' h₁ h₂
  have hrad : ∀ u : ↥U, (∀ c, β' u c = 0) → ((π₁ u : ↥V) : G) = 1 := by
    intro u hu
    by_contra hne
    obtain ⟨c, hc, hc1⟩ := hnd₁ _ (hπ₁ u) hne
    have h := hu ⟨c, hc⟩
    simp only [hβ'] at h
    rw [h] at hc1
    exact zero_ne_one hc1
  let g : ↥U → ↥V₂ := fun u => ⟨((π₁ u : ↥V) : G)⁻¹ * u, hπ₂ u⟩
  have hmaps : ∀ u ∈ (Finset.univ.filter fun a => ∀ c, β' a c = 0),
      g u ∈ (Finset.univ.filter fun c => ∀ a, β' a c = 0) := by
    intro u hu
    rw [Finset.mem_filter] at hu ⊢
    refine ⟨Finset.mem_univ _, fun u' => ?_⟩
    have hu1 := hrad u hu.2
    have hu2 : (u : G) ∈ V₂ := by
      have := hπ₂ u
      rwa [hu1, inv_one, one_mul] at this
    obtain ⟨a, ha, c, hc, hac, hβac⟩ := hU u' u'.2
    obtain ⟨a', ha', c', hc', hac', hβac'⟩ := hU (u' * u) (U.mul_mem u'.2 u.2)
    have e : a * (c * u) = a' * c' := by rw [← mul_assoc, ← hac, ← hac']
    obtain ⟨rfl, rfl⟩ := decomp_unique hinf ha (V₂.mul_mem hc hu2) ha' hc' e
    have hπ : ((π₁ u' : ↥V) : G) = a := hπa u' ha hc hac
    show β ((π₁ u' : ↥V) : G) (((π₁ u : ↥V) : G)⁻¹ * u) = 0
    rw [hu1, inv_one, one_mul, hπ]
    have := hβ₂ a ha c hc u hu2
    rw [hβac', hβac, zero_add] at this
    exact this.symm
  have hinj : Set.InjOn g (Finset.univ.filter fun a => ∀ c, β' a c = 0) := by
    intro u hu u' hu' huu
    rw [Finset.coe_filter] at hu hu'
    have h1 := hrad u hu.2
    have h2 := hrad u' hu'.2
    have h3 := congrArg Subtype.val huu
    simp only [g, h1, h2, inv_one, one_mul] at h3
    exact Subtype.ext h3
  have hle := Finset.card_le_card_of_injOn g hmaps hinj
  have hpos : 0 < (Finset.univ.filter fun c => ∀ a, β' a c = 0).card := by
    refine Finset.card_pos.mpr ⟨1, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun a => h0 _ (hπ₁ a)⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  rw [← hcount]
  exact Nat.mul_le_mul_left _ hle

end Singular

section Hyp

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ : Subgroup G} {n : ℕ}

theorem card_eq_of_hyp121 (hyp : Hyp121 G T L V V₁ V₂ n) [IsMulCommutative ↥V] :
    Nat.card V₁ = 2 ^ n ∧ Nat.card V₂ = 2 ^ n ∧ Nat.card V = 2 ^ n * 2 ^ n := by
  obtain ⟨hc₁, hnat₁⟩ := hyp.nat₁
  obtain ⟨hc₂, hnat₂⟩ := hyp.nat₂
  have h1 := G64.BinaryNaturalSL.card_eq hnat₁
  have h2 := G64.BinaryNaturalSL.card_eq hnat₂
  have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
  have hV₂V : V₂ ≤ V := hyp.sup ▸ le_sup_right
  have hcomm : ∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm (⟨a, hV₁V ha⟩ : ↥V) ⟨b, hV₂V hb⟩)
  have h3 := B2F.card_sup_mul_card_inf_of_commute hcomm
  rw [hyp.sup, hyp.inf, Subgroup.card_bot, mul_one, h1, h2] at h3
  exact ⟨h1, h2, h3⟩

theorem le_rParam (hyp : Hyp121 G T L V V₁ V₂ n) {β : G → G → ZMod 2}
    (hβ : IsDualPairing121 L V₁ V₂ β)
    (hNV : Subgroup.normalizer (V : Set G) = Subgroup.normalizer (L : Set G))
    (hsing : ∀ U : Subgroup G, U ≤ V →
      ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (L : Set G) →
        ∀ u ∈ U, IsSingular121 V₁ V₂ β u) :
    (n : ℕ∞) ≤ rParam V := by
  have hVe := Sec121Thm.isElemAbelian_of_isPrimeReduced hyp.le hyp.reduced
  have := hVe.1
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using hVe.2 x x.2)⟩
  obtain ⟨-, hc₂, hcV⟩ := card_eq_of_hyp121 hyp
  have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
  have hV₂V : V₂ ≤ V := hyp.sup ▸ le_sup_right
  refine le_iInf₂ fun U hU => ?_
  have hC : ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (L : Set G) := hNV ▸ hU.2
  have hcard := card_le_of_forall_singular hV₁V hV₂V hyp.sup hyp.inf hβ hU.1 (hsing U hU.1 hC)
  have h := E3.card_eq_two_pow_mul hV2 hU.1
  have h2 : 2 ^ n * 2 ^ n ≤ 2 ^ mQuot V U * 2 ^ n := by
    rw [← hcV, h]
    exact Nat.mul_le_mul_left _ (hcard.trans hc₂.le)
  have h3 : 2 ^ n ≤ 2 ^ mQuot V U := Nat.le_of_mul_le_mul_right h2 (by positivity)
  exact_mod_cast (Nat.pow_le_pow_iff_right (by norm_num)).mp h3

theorem mem_centralizer_of_hyp121 (hyp : Hyp121 G T L V V₁ V₂ n) [IsMulCommutative ↥V]
    {X : Subgroup G} [IsMulCommutative ↥X] (hXV : X ≤ V)
    (hLX : L ≤ Subgroup.normalizer (X : Set G))
    (hnat : BinaryNaturalSL (V := ↥X) (autOn L X) ⊤ ⊥ n 1) {m : G}
    (hm : m ∈ Subgroup.normalizer (L : Set G)) (hmX : m ∈ Subgroup.centralizer (X : Set G)) :
    m ∈ Subgroup.centralizer (V : Set G) := by
  have hMV := Sec121Q.normalizer_le_of_hyp121 hyp
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := Subgroup.le_normalizer.trans hMV
  have hmX' := mem_centralizer_iff_conj.mp hmX
  have hcomm : ∀ y ∈ autOn L V, conjAct V ⟨m, hMV hm⟩ * y = y * conjAct V ⟨m, hMV hm⟩ := by
    intro y hy
    obtain ⟨⟨l, hl⟩, rfl⟩ := (A4.mem_autOn_iff hLV).mp hy
    set k := m * l * m⁻¹ * l⁻¹ with hk
    have hkL : k ∈ L := L.mul_mem ((Subgroup.mem_normalizer_iff.mp hm l).mp hl) (L.inv_mem hl)
    have hkX : k ∈ Subgroup.centralizer (X : Set G) := by
      refine mem_centralizer_iff_conj.mpr fun x hx => ?_
      have h1 : l⁻¹ * x * l ∈ X := by
        have := (Subgroup.mem_normalizer_iff.mp (hLX (L.inv_mem hl)) x).mp hx
        simpa using this
      have h2 : m⁻¹ * (l⁻¹ * x * l) * m = l⁻¹ * x * l := by
        have := hmX' _ h1
        calc m⁻¹ * (l⁻¹ * x * l) * m = m⁻¹ * (m * (l⁻¹ * x * l) * m⁻¹) * m := by rw [this]
          _ = l⁻¹ * x * l := by group
      calc k * x * k⁻¹ = m * (l * (m⁻¹ * (l⁻¹ * x * l) * m) * l⁻¹) * m⁻¹ := by rw [hk]; group
        _ = m * x * m⁻¹ := by rw [h2]; group
        _ = x := hmX' x hx
    have hkV := Sec121Q.inf_centralizer_le_centralizer_of_hyp121 hyp hXV hLX hnat ⟨hkL, hkX⟩
    refine MulEquiv.ext fun v => Subtype.ext ?_
    simp only [MulAut.mul_apply, InternalSec.coe_conjAct_apply, A4.actionOn_apply_coe]
    have hw : l * m * (v : G) * m⁻¹ * l⁻¹ ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (V : Set G)).mul_mem (hLV hl) (hMV hm)) v).mp v.2
      simpa [mul_assoc] using this
    have hkw := (mem_centralizer_iff_conj.mp hkV) _ hw
    have e1 : m * l = k * l * m := by rw [hk]; group
    calc m * (l * (v : G) * l⁻¹) * m⁻¹ = (m * l) * v * (m * l)⁻¹ := by group
      _ = (k * l * m) * v * (k * l * m)⁻¹ := by rw [e1]
      _ = k * (l * m * v * m⁻¹ * l⁻¹) * k⁻¹ := by group
      _ = l * m * v * m⁻¹ * l⁻¹ := hkw
      _ = l * (m * v * m⁻¹) * l⁻¹ := by group
  have h1 := Sec121Q.eq_one_of_commute_of_hyp121 hyp hcomm
  exact A4.conjAct_eq_one_iff.mp h1

theorem conj_mem_of_hyp121 (hyp : Hyp121 G T L V V₁ V₂ n) [IsMulCommutative ↥V] {m : G}
    (hm : m ∈ Subgroup.normalizer (L : Set G)) :
    ((∀ a ∈ V₁, m * a * m⁻¹ ∈ V₁) ∧ ∀ c ∈ V₂, m * c * m⁻¹ ∈ V₂) ∨
      ∀ a ∈ V₁, m * a * m⁻¹ ∈ V₂ := by
  have hn2 : 2 ≤ n := by rcases hyp.rank with h | h <;> omega
  obtain ⟨hc₁, hnat₁⟩ := hyp.nat₁
  obtain ⟨hc₂, hnat₂⟩ := hyp.nat₂
  have hV₁ : V₁ ≤ V := hyp.sup ▸ le_sup_left
  have hV₂ : V₂ ≤ V := hyp.sup ▸ le_sup_right
  have hMV := Sec121Q.normalizer_le_of_hyp121 hyp
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := Subgroup.le_normalizer.trans hMV
  set Λ := autOn L V with hΛ
  set W₁ := V₁.subgroupOf V with hW₁
  set W₂ := V₂.subgroupOf V with hW₂
  have hinf' : W₁ ⊓ W₂ = ⊥ := InternalSec.inf_subgroupOf_eq_bot hyp.inf
  have hsup' : W₁ ⊔ W₂ = ⊤ := InternalSec.sup_subgroupOf_eq_top hV₁ hV₂ hyp.sup
  have hinf'' : W₂ ⊓ W₁ = ⊥ := by rw [inf_comm]; exact hinf'
  have hsup'' : W₂ ⊔ W₁ = ⊤ := by rw [sup_comm]; exact hsup'
  have hI₁ : H.Pair.IsInv Λ W₁ := InternalSec.autOn_inv_subgroupOf hyp.norm₁
  have hI₂ : H.Pair.IsInv Λ W₂ := InternalSec.autOn_inv_subgroupOf hyp.norm₂
  have hne : ∀ {X : Subgroup G}, X ≤ V → X ≠ ⊥ → X.subgroupOf V ≠ ⊥ := fun hX hX0 h =>
    hX0 (by
      have h1 := disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp h)
      rwa [inf_eq_left.mpr hX] at h1)
  have hIrr₁ : H.Pair.IsIrr Λ W₁ :=
    ⟨hne hV₁ (Sec121Q.ne_bot_of_natural hn2 hnat₁), fun U hU hUi =>
      InternalSec.irr_subgroupOf hLV (Sec121Q.eq_bot_or_eq_of_natural hyp.norm₁ hnat₁) U hU hUi⟩
  have hIrr₂ : H.Pair.IsIrr Λ W₂ :=
    ⟨hne hV₂ (Sec121Q.ne_bot_of_natural hn2 hnat₂), fun U hU hUi =>
      InternalSec.irr_subgroupOf hLV (Sec121Q.eq_bot_or_eq_of_natural hyp.norm₂ hnat₂) U hU hUi⟩
  have hniso₁ : ¬ H.Pair.IsoMod Λ W₁ W₂ := fun h =>
    hyp.dual (Sec121.isXSectionIso₂_of_isoMod hV₁ hV₂ hLV h)
  have hniso₂ : ¬ H.Pair.IsoMod Λ W₂ W₁ := fun h => hniso₁ (h.symm hI₂)
  set c := conjAct V ⟨m, hMV hm⟩ with hc
  have hcN : c ∈ Subgroup.normalizer (Λ : Set (MulAut ↥V)) := by
    have hconj : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G)), ∀ y ∈ Λ,
        conjAct V ⟨g, hMV hg⟩ * y * (conjAct V ⟨g, hMV hg⟩)⁻¹ ∈ Λ := by
      intro g hg y hy
      exact InternalSec.autOn_normal_of le_rfl _ (Setup.mem_autOn_iff.mpr ⟨_, hg, rfl⟩) y hy
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hconj m hm y hy, fun hy => ?_⟩
    have h1 := hconj m⁻¹ (Subgroup.inv_mem _ hm) _ hy
    have e : conjAct V ⟨m⁻¹, hMV (Subgroup.inv_mem _ hm)⟩ = c⁻¹ := by
      rw [hc, ← map_inv]
      rfl
    rw [e, inv_inv] at h1
    simpa [mul_assoc] using h1
  have hmap₁ := H.Pair.map_eq_or_map_eq hinf' hsup' hI₁ hI₂ hIrr₁ hIrr₂ hniso₁ hcN
  have hmap₂ := H.Pair.map_eq_or_map_eq hinf'' hsup'' hI₂ hI₁ hIrr₂ hIrr₁ hniso₂ hcN
  have hmem : ∀ {A B : Subgroup G} (hA : A ≤ V),
      (A.subgroupOf V).map c.toMonoidHom = B.subgroupOf V → ∀ a ∈ A, m * a * m⁻¹ ∈ B := by
    intro A B hA h a ha
    have : c ⟨a, hA ha⟩ ∈ (A.subgroupOf V).map c.toMonoidHom :=
      ⟨⟨a, hA ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    rw [h, Subgroup.mem_subgroupOf, hc, InternalSec.coe_conjAct_apply] at this
    exact this
  rcases hmap₁ with h1 | h1
  · left
    refine ⟨hmem hV₁ h1, ?_⟩
    rcases hmap₂ with h2 | h2
    · exact hmem hV₂ h2
    · exfalso
      have h3 : W₂ = W₁ :=
        Subgroup.map_injective (f := c.toMonoidHom) (fun a b h => c.injective h) (h2.trans h1.symm)
      apply hIrr₁.1
      rw [← hinf', h3, inf_idem]
  · right
    exact hmem hV₁ h1

theorem four_mul_card_le (hyp : Hyp121 G T L V V₁ V₂ n) [IsMulCommutative ↥V] {m : G}
    (hm : m ∈ Subgroup.normalizer (L : Set G)) (hmV : m ∉ Subgroup.centralizer (V : Set G)) :
    4 * Nat.card ↥(V ⊓ Subgroup.centralizer ({m} : Set G)) ≤ Nat.card V := by
  have hn2 : 2 ≤ n := by rcases hyp.rank with h | h <;> omega
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨hcard₁, hcard₂, hcardV⟩ := card_eq_of_hyp121 hyp
  obtain ⟨hc₁, hnat₁⟩ := hyp.nat₁
  obtain ⟨hc₂, hnat₂⟩ := hyp.nat₂
  have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
  have hV₂V : V₂ ≤ V := hyp.sup ▸ le_sup_right
  have hcommV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥V) ⟨b, hb⟩)
  set C := V ⊓ Subgroup.centralizer ({m} : Set G) with hC
  rcases conj_mem_of_hyp121 hyp hm with ⟨h₁, h₂⟩ | h₁₂
  ·
    have hprop : ∀ {X : Subgroup G} [IsMulCommutative ↥X], X ≤ V →
        L ≤ Subgroup.normalizer (X : Set G) → BinaryNaturalSL (V := ↥X) (autOn L X) ⊤ ⊥ n 1 →
          2 * Nat.card ↥(X ⊓ Subgroup.centralizer ({m} : Set G)) ≤ Nat.card X := by
      intro X _ hXV hLX hnat
      have hlt : ¬ X ≤ Subgroup.centralizer ({m} : Set G) := by
        intro hle
        refine hmV (mem_centralizer_of_hyp121 hyp hXV hLX hnat hm ?_)
        refine mem_centralizer_iff_conj.mpr fun x hx => ?_
        exact mem_centralizer_singleton_iff_conj.mp (hle hx)
      set K := (X ⊓ Subgroup.centralizer ({m} : Set G)).subgroupOf X
      have hK : K.index ≠ 1 := by
        rw [Ne, Subgroup.index_eq_one]
        intro htop
        apply hlt
        intro x hx
        have : (⟨x, hx⟩ : ↥X) ∈ K := htop ▸ Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp this).2
      have h1 := K.card_mul_index
      have h2 : Nat.card K = Nat.card ↥(X ⊓ Subgroup.centralizer ({m} : Set G)) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
      have h3 : 2 ≤ K.index := by
        have := K.index_ne_zero_of_finite
        omega
      rw [← h2, ← h1, mul_comm]
      exact Nat.mul_le_mul_left _ h3
    have hC₁ := hprop hV₁V hyp.norm₁ hnat₁
    have hC₂ := hprop hV₂V hyp.norm₂ hnat₂
    have hle : C ≤ (V₁ ⊓ Subgroup.centralizer ({m} : Set G)) ⊔
        (V₂ ⊓ Subgroup.centralizer ({m} : Set G)) := by
      intro v hv
      have hv' : v ∈ V₁ ⊔ V₂ := hyp.sup ▸ hv.1
      obtain ⟨a, ha, c, hc, rfl⟩ :=
        Sec121Thm.exists_mul_of_mem_sup (fun a ha b hb => hcommV a (hV₁V ha) b (hV₂V hb)) hv'
      have hfix := mem_centralizer_singleton_iff_conj.mp hv.2
      have e : m * a * m⁻¹ * (m * c * m⁻¹) = a * c := by rw [← hfix]; group
      obtain ⟨ea, ec⟩ := decomp_unique hyp.inf (h₁ a ha) (h₂ c hc) ha hc e
      exact Subgroup.mul_mem_sup ⟨ha, mem_centralizer_singleton_iff_conj.mpr ea⟩
        ⟨hc, mem_centralizer_singleton_iff_conj.mpr ec⟩
    have hsup := B2F.card_sup_mul_card_inf_of_commute
      (A := V₁ ⊓ Subgroup.centralizer ({m} : Set G)) (B := V₂ ⊓ Subgroup.centralizer ({m} : Set G))
      (fun a ha b hb => hcommV a (hV₁V ha.1) b (hV₂V hb.1))
    have hinf1 : 0 < Nat.card ↥((V₁ ⊓ Subgroup.centralizer ({m} : Set G)) ⊓
        (V₂ ⊓ Subgroup.centralizer ({m} : Set G))) := Nat.card_pos
    have hsup' : Nat.card ↥((V₁ ⊓ Subgroup.centralizer ({m} : Set G)) ⊔
        (V₂ ⊓ Subgroup.centralizer ({m} : Set G))) ≤
        Nat.card ↥(V₁ ⊓ Subgroup.centralizer ({m} : Set G)) *
          Nat.card ↥(V₂ ⊓ Subgroup.centralizer ({m} : Set G)) := by
      rw [← hsup]
      exact Nat.le_mul_of_pos_right _ hinf1
    calc 4 * Nat.card C ≤ 4 * Nat.card ↥((V₁ ⊓ Subgroup.centralizer ({m} : Set G)) ⊔
          (V₂ ⊓ Subgroup.centralizer ({m} : Set G))) :=
          Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hle)
      _ ≤ 4 * (Nat.card ↥(V₁ ⊓ Subgroup.centralizer ({m} : Set G)) *
          Nat.card ↥(V₂ ⊓ Subgroup.centralizer ({m} : Set G))) := Nat.mul_le_mul_left _ hsup'
      _ = (2 * Nat.card ↥(V₁ ⊓ Subgroup.centralizer ({m} : Set G))) *
          (2 * Nat.card ↥(V₂ ⊓ Subgroup.centralizer ({m} : Set G))) := by ring
      _ ≤ Nat.card V₁ * Nat.card V₂ := Nat.mul_le_mul hC₁ hC₂
      _ = Nat.card V := by rw [hcard₁, hcard₂, hcardV]
  ·
    have hinf : C ⊓ V₁ = ⊥ := by
      rw [eq_bot_iff]
      rintro a ⟨⟨-, hac⟩, ha⟩
      have h1 := mem_centralizer_singleton_iff_conj.mp hac
      have h2 : a ∈ V₂ := h1 ▸ h₁₂ a ha
      have : a ∈ V₁ ⊓ V₂ := ⟨ha, h2⟩
      rwa [hyp.inf] at this
    have hsup := B2F.card_sup_mul_card_inf_of_commute (A := C) (B := V₁)
      (fun a ha b hb => hcommV a ha.1 b (hV₁V hb))
    rw [hinf, Subgroup.card_bot, mul_one] at hsup
    have hle : Nat.card ↥(C ⊔ V₁) ≤ Nat.card V := Subgroup.card_le_of_le (sup_le inf_le_left hV₁V)
    have h3 : Nat.card C * 2 ^ n ≤ 2 ^ n * 2 ^ n := by
      rw [← hcardV, ← hcard₁, ← hsup]
      exact hle
    have h5 : Nat.card C ≤ 2 ^ n := Nat.le_of_mul_le_mul_right h3 (by positivity)
    calc 4 * Nat.card C ≤ 4 * 2 ^ n := Nat.mul_le_mul_left _ h5
      _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul_right _ h4
      _ = Nat.card V := hcardV.symm

theorem exists_transvection (hyp : Hyp121 G T L V V₁ V₂ n) [IsMulCommutative ↥V]
    {β : G → G → ZMod 2} (hβ : IsDualPairing121 L V₁ V₂ β) :
    ∃ l ∈ L, l ∉ Subgroup.centralizer (V : Set G) ∧
      l ^ 2 ∈ Subgroup.centralizer (V : Set G) ∧
        Nat.card V ≤ 4 * Nat.card ↥(V ⊓ Subgroup.centralizer ({l} : Set G)) := by
  classical
  have hn2 : 2 ≤ n := by rcases hyp.rank with h | h <;> omega
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨hcard₁, hcard₂, hcardV⟩ := card_eq_of_hyp121 hyp
  obtain ⟨hc₁, hnat₁⟩ := hyp.nat₁
  obtain ⟨hc₂, hnat₂⟩ := hyp.nat₂
  have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
  have hV₂V : V₂ ≤ V := hyp.sup ▸ le_sup_right
  have hVe := Sec121Thm.isElemAbelian_of_isPrimeReduced hyp.le hyp.reduced
  have hcommV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥V) ⟨b, hb⟩)
  obtain ⟨hβ₁, hβ₂, hnd₁, hnd₂, hβL⟩ := hβ
  have h01 : ∀ e : ZMod 2, e = 0 ∨ e = 1 := by decide
  obtain ⟨⟨c₀, hc₀⟩, hc₀1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Sec121Q.ne_bot_of_natural hn2 hnat₂)
  have hc₀1' : c₀ ≠ 1 := fun h => hc₀1 (Subtype.ext h)
  obtain ⟨a₁, ha₁, ha₁c⟩ := hnd₂ c₀ hc₀ hc₀1'
  obtain ⟨A, hA, hAmem, hAcard⟩ :=
    exists_ker (X := V₁) (fun a => β a c₀) (fun a ha b hb => hβ₁ a ha b hb c₀ hc₀)
  have hAc := hAcard a₁ ha₁ (by rw [ha₁c]; exact one_ne_zero)
  have hA2 : 1 < Nat.card A := by omega
  obtain ⟨⟨x, hxA⟩, hx1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp ((Subgroup.one_lt_card_iff_ne_bot A).mp hA2)
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hx : x ∈ V₁ := hA hxA
  have hxc₀ : β x c₀ = 0 := (hAmem x hx).mp hxA
  have hxx : (⟨x, hx⟩ : ↥V₁) * ⟨x, hx⟩ = 1 := by
    apply Subtype.ext
    have := hVe.2 x (hV₁V hx)
    simpa [pow_two] using this
  set τf : ↥V₁ → ↥V₁ := fun a => if β a c₀ = 0 then a else a * ⟨x, hx⟩ with hτf
  have hτ_mul : ∀ a b, τf (a * b) = τf a * τf b := by
    intro a b
    have hab : β ((a : G) * b) c₀ = β a c₀ + β b c₀ := hβ₁ a a.2 b b.2 c₀ hc₀
    rcases h01 (β a c₀) with ha | ha <;> rcases h01 (β b c₀) with hb | hb
    · have h : β ((a : G) * b) c₀ = 0 := by rw [hab, ha, hb]; decide
      simp only [hτf, Subgroup.coe_mul, h, ha, hb, ↓reduceIte]
    · have h : β ((a : G) * b) c₀ = 1 := by rw [hab, ha, hb]; decide
      simp only [hτf, Subgroup.coe_mul, h, ha, hb, one_ne_zero, ↓reduceIte]
      rw [mul_assoc]
    · have h : β ((a : G) * b) c₀ = 1 := by rw [hab, ha, hb]; decide
      simp only [hτf, Subgroup.coe_mul, h, ha, hb, one_ne_zero, ↓reduceIte]
      exact mul_right_comm a b _
    · have h : β ((a : G) * b) c₀ = 0 := by rw [hab, ha, hb]; decide
      simp only [hτf, Subgroup.coe_mul, h, ha, hb, one_ne_zero, ↓reduceIte]
      rw [mul_mul_mul_comm, hxx, mul_one]
  have hτ_inv : ∀ a, τf (τf a) = a := by
    intro a
    rcases h01 (β a c₀) with ha | ha
    · simp only [hτf, ha, ↓reduceIte]
    · have h : β ((a : G) * x) c₀ = 1 := by
        rw [hβ₁ a a.2 x hx c₀ hc₀, ha, hxc₀, add_zero]
      simp only [hτf, ha, h, Subgroup.coe_mul, one_ne_zero, ↓reduceIte]
      rw [mul_assoc, hxx, mul_one]
  let τ : MulAut ↥V₁ :=
    { toFun := τf
      invFun := τf
      left_inv := hτ_inv
      right_inv := hτ_inv
      map_mul' := hτ_mul }
  have hτmem : τ ∈ autOn L V₁ := by
    rw [G64.BinaryNaturalSL.eq_top hnat₁]
    exact Subgroup.mem_top _
  obtain ⟨⟨l, hl⟩, hlτ⟩ := (A4.mem_autOn_iff hyp.norm₁).mp hτmem
  have hlact : ∀ (a : G) (ha : a ∈ V₁), l * a * l⁻¹ = ((τf ⟨a, ha⟩ : ↥V₁) : G) := by
    intro a ha
    have := A4.actionOn_apply_coe hyp.norm₁ ⟨l, hl⟩ ⟨a, ha⟩
    rw [hlτ] at this
    exact this.symm
  have hlact' : ∀ (a : G) (ha : a ∈ V₁), l⁻¹ * a * l = ((τf ⟨a, ha⟩ : ↥V₁) : G) := by
    intro a ha
    have h1 := hlact _ (τf ⟨a, ha⟩).2
    have h2 : τf (τf ⟨a, ha⟩) = ⟨a, ha⟩ := hτ_inv _
    rw [show (⟨((τf ⟨a, ha⟩ : ↥V₁) : G), (τf ⟨a, ha⟩).2⟩ : ↥V₁) = τf ⟨a, ha⟩ from rfl, h2] at h1
    calc l⁻¹ * a * l = l⁻¹ * (l * ((τf ⟨a, ha⟩ : ↥V₁) : G) * l⁻¹) * l := by rw [h1]
      _ = ((τf ⟨a, ha⟩ : ↥V₁) : G) := by group
  have hτa₁ : ((τf ⟨a₁, ha₁⟩ : ↥V₁) : G) = a₁ * x := by
    simp [hτf, ha₁c]
  have hlV : l ∉ Subgroup.centralizer (V : Set G) := by
    intro h
    have h1 := (mem_centralizer_iff_conj.mp h) a₁ (hV₁V ha₁)
    rw [hlact a₁ ha₁, hτa₁] at h1
    exact hx1' (mul_eq_left.mp h1)
  have hl2 : l ^ 2 ∈ Subgroup.centralizer (V : Set G) := by
    refine Sec121Q.inf_centralizer_le_centralizer_of_hyp121 hyp hV₁V hyp.norm₁ hnat₁
      ⟨L.pow_mem hl 2, mem_centralizer_iff_conj.mpr fun a ha => ?_⟩
    have h1 := hlact _ (τf ⟨a, ha⟩).2
    rw [show (⟨((τf ⟨a, ha⟩ : ↥V₁) : G), (τf ⟨a, ha⟩).2⟩ : ↥V₁) = τf ⟨a, ha⟩ from rfl,
      hτ_inv] at h1
    calc l ^ 2 * a * (l ^ 2)⁻¹ = l * (l * a * l⁻¹) * l⁻¹ := by rw [pow_two]; group
      _ = a := by rw [hlact a ha, h1]
  obtain ⟨c₁, hc₁, hxc₁⟩ := hnd₁ x hx hx1'
  obtain ⟨B, hB, hBmem, hBcard⟩ :=
    exists_ker (X := V₂) (fun c => β x c) (fun c hc d hd => hβ₂ x hx c hc d hd)
  have hBc := hBcard c₁ hc₁ (by rw [hxc₁]; exact one_ne_zero)
  have hAC : A ≤ V ⊓ Subgroup.centralizer ({l} : Set G) := by
    intro a haA
    have ha := hA haA
    have hac : β a c₀ = 0 := (hAmem a ha).mp haA
    refine ⟨hV₁V ha, mem_centralizer_singleton_iff_conj.mpr ?_⟩
    rw [hlact a ha]
    simp [hτf, hac]
  have hBC : B ≤ V ⊓ Subgroup.centralizer ({l} : Set G) := by
    intro c hcB
    have hc := hB hcB
    have hxc : β x c = 0 := (hBmem c hc).mp hcB
    refine ⟨hV₂V hc, mem_centralizer_singleton_iff_conj.mpr ?_⟩
    set c' := l * c * l⁻¹ with hc'
    have hc'V : c' ∈ V₂ := (Subgroup.mem_normalizer_iff.mp (hyp.norm₂ hl) c).mp hc
    have hβeq : ∀ a ∈ V₁, β a c' = β a c := by
      intro a ha
      have h1 := hβL l⁻¹ (L.inv_mem hl) a ha c' hc'V
      have e1 : l⁻¹ * c' * l⁻¹⁻¹ = c := by rw [hc']; group
      rw [e1, inv_inv, hlact' a ha] at h1
      rw [← h1]
      rcases h01 (β a c₀) with h0 | h0
      · simp [hτf, h0]
      · simp only [hτf, h0, one_ne_zero, ↓reduceIte, Subgroup.coe_mul]
        rw [hβ₁ a ha x hx c hc, hxc, add_zero]
    by_contra hne
    have hne' : c' * c⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.mp h)
    obtain ⟨a, ha, hac⟩ := hnd₂ _ (V₂.mul_mem hc'V (V₂.inv_mem hc)) hne'
    have h1 := hβ₂ a ha c' hc'V c⁻¹ (V₂.inv_mem hc)
    have h2 := hβ₂ a ha c hc c⁻¹ (V₂.inv_mem hc)
    rw [mul_inv_cancel] at h2
    have h3 : β a 1 = 0 := by
      have := hβ₂ a ha 1 V₂.one_mem 1 V₂.one_mem
      rw [mul_one] at this
      simpa using this
    rw [hac, hβeq a ha] at h1
    rw [h3] at h2
    rw [← h2] at h1
    exact one_ne_zero h1
  have hABinf : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have : y ∈ V₁ ⊓ V₂ := ⟨hA hy.1, hB hy.2⟩
    rwa [hyp.inf] at this
  have hsup := B2F.card_sup_mul_card_inf_of_commute (A := A) (B := B)
    (fun a ha b hb => hcommV a (hV₁V (hA ha)) b (hV₂V (hB hb)))
  rw [hABinf, Subgroup.card_bot, mul_one] at hsup
  have hle : Nat.card ↥(A ⊔ B) ≤ Nat.card ↥(V ⊓ Subgroup.centralizer ({l} : Set G)) :=
    Subgroup.card_le_of_le (sup_le hAC hBC)
  refine ⟨l, hl, hlV, hl2, ?_⟩
  calc Nat.card V = 2 ^ n * 2 ^ n := hcardV
    _ = (2 * Nat.card A) * (2 * Nat.card B) := by rw [hAc, hBc, hcard₁, hcard₂]
    _ = 4 * Nat.card ↥(A ⊔ B) := by rw [hsup]; ring
    _ ≤ 4 * Nat.card ↥(V ⊓ Subgroup.centralizer ({l} : Set G)) := Nat.mul_le_mul_left _ hle

omit [Finite G] in
theorem card_fixV_zpowers_convI (hV : IsElemAbelian 2 V) (g : Subgroup.normalizer (V : Set G)) :
    Nat.card (fixV (Subgroup.zpowers (convI hV g))) =
      Nat.card ↥(V ⊓ Subgroup.centralizer ({(g : G)} : Set G)) := by
  have hmem : ∀ w : IntMod V hV, w ∈ fixV (Subgroup.zpowers (convI hV g)) ↔
      w.val ∈ V ⊓ Subgroup.centralizer ({(g : G)} : Set G) := by
    intro w
    rw [Subgroup.mem_inf, mem_centralizer_singleton_iff_conj]
    constructor
    · intro h
      have h1 := congrArg IntMod.val (h _ (Subgroup.mem_zpowers _))
      rw [convI_apply_val] at h1
      exact ⟨w.val_mem, h1⟩
    · rintro ⟨-, h⟩
      have h' : convI hV g w = w := by
        refine IntMod.val_injective ?_
        rw [convI_apply_val]
        exact h
      exact B1.zpowers_fix h'
  exact Nat.card_congr
    { toFun := fun w => ⟨w.1.val, (hmem w.1).mp w.2⟩
      invFun := fun v => ⟨IntMod.mk hV ⟨v, v.2.1⟩, (hmem _).mpr v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem two_le_rkIdx {W : Type*} [Group W] [Finite W] {k : ℕ} (hW : Nat.card W = 2 ^ k)
    {C : Subgroup W} (hC : 4 * Nat.card C ≤ Nat.card W) : 2 ≤ rkIdx C := by
  have h := C.card_mul_index
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hW ▸ C.index_dvd_card)
  unfold rkIdx
  rw [hj, padicValNat.prime_pow]
  by_contra hlt
  have h2 : 2 ^ j ≤ 2 := by
    calc 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 := by norm_num
  rw [hj] at h
  have hpos : 0 < Nat.card C := Nat.card_pos
  nlinarith

theorem rkIdx_le_two {W : Type*} [Group W] [Finite W] {k : ℕ} (hW : Nat.card W = 2 ^ k)
    {C : Subgroup W} (hC : Nat.card W ≤ 4 * Nat.card C) : rkIdx C ≤ 2 := by
  have h := C.card_mul_index
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hW ▸ C.index_dvd_card)
  unfold rkIdx
  rw [hj, padicValNat.prime_pow]
  by_contra hlt
  have h8 : 8 ≤ 2 ^ j := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hj] at h
  have hpos : 0 < Nat.card C := Nat.card_pos
  nlinarith

theorem mParam_eq_two (hyp : Hyp121 G T L V V₁ V₂ n) {β : G → G → ZMod 2}
    (hβ : IsDualPairing121 L V₁ V₂ β) (hV : IsElemAbelian 2 V) :
    mParam (autI hV (Subgroup.normalizer (L : Set G))) = 2 := by
  have := hV.1
  have hMV := Sec121Q.normalizer_le_of_hyp121 hyp
  obtain ⟨-, -, hcardV⟩ := card_eq_of_hyp121 hyp
  have hW : Nat.card (IntMod V hV) = 2 ^ (n + n) := by
    rw [pow_add]
    exact hcardV
  have hlow : ∀ t ∈ autI hV (Subgroup.normalizer (L : Set G)), orderOf t = 2 →
      2 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
    intro t ht hot
    obtain ⟨g, hgM, rfl⟩ := (mem_autI hV).mp ht
    have hg1 : (g : G) ∉ Subgroup.centralizer (V : Set G) := fun h => by
      rw [(convI_eq_one_iff hV g).mpr h, orderOf_one] at hot
      exact absurd hot (by norm_num)
    refine two_le_rkIdx hW ?_
    rw [card_fixV_zpowers_convI hV g]
    exact four_mul_card_le hyp hgM hg1
  obtain ⟨l, hl, hlV, hl2, hlcard⟩ := exists_transvection hyp hβ
  have hlN : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hl
  set t₀ := convI hV ⟨l, hMV hlN⟩ with ht₀
  have ht₀M : t₀ ∈ autI hV (Subgroup.normalizer (L : Set G)) := convI_mem_autI hV hlN _
  have hot₀ : orderOf t₀ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [ht₀, ← map_pow]
      exact (convI_eq_one_iff hV _).mpr (by simpa using hl2)
    · intro h
      exact hlV ((convI_eq_one_iff hV _).mp h)
  have hrk₀ : rkIdx (fixV (Subgroup.zpowers t₀)) ≤ 2 := by
    refine rkIdx_le_two hW ?_
    rw [card_fixV_zpowers_convI hV]
    exact hlcard
  have heven : Even (Nat.card (autI hV (Subgroup.normalizer (L : Set G)))) := by
    have h2 : orderOf (⟨t₀, ht₀M⟩ : ↥(autI hV (Subgroup.normalizer (L : Set G)))) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact hot₀
    have := orderOf_dvd_natCard (⟨t₀, ht₀M⟩ : ↥(autI hV (Subgroup.normalizer (L : Set G))))
    rw [h2] at this
    exact even_iff_two_dvd.mpr this
  unfold mParam
  simp only [heven, ↓reduceIte]
  refine le_antisymm (Nat.sInf_le ⟨t₀, ht₀M, hot₀, ?_⟩) (le_csInf ⟨_, t₀, ht₀M, hot₀, rfl⟩ ?_)
  · exact le_antisymm (hlow t₀ ht₀M hot₀) hrk₀
  · rintro k ⟨t, ht, hot, rfl⟩
    exact hlow t ht hot

end Hyp

end Sec1212

open Sec1212 Sec121Thm

theorem lem1212_of (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (h1211 : Lem1211) :
    ∀ (G : Type) [Group G] [Finite G] (T L V V₁ V₂ : Subgroup G) (n : ℕ) (β : G → G → ZMod 2),
      Hyp121 G T L V V₁ V₂ n → IsDualPairing121 L V₁ V₂ β →
        (∀ U : Subgroup G, U ≤ V →
          ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (L : Set G) →
            ∀ u ∈ U, IsSingular121 V₁ V₂ β u) ∧
        ∀ hV : IsElemAbelian 2 V, (n : ℕ∞) ≤ rParam V ∧ sParam hV = 2 ∧
          mParam (autI hV (Subgroup.normalizer (L : Set G))) = 2 := by
  intro G _ _ T L V V₁ V₂ n β hyp hβ
  have hone : ∀ U : Subgroup G, U ≤ V →
      ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (L : Set G) →
        ∀ u ∈ U, IsSingular121 V₁ V₂ β u :=
    fun U hUV hC u hu => lem1212_one_of h1211 hyp hβ U hUV hC u hu
  refine ⟨hone, fun hV => ?_⟩
  have := hV.1
  have hn2 : 2 ≤ n := by rcases hyp.rank with h | h <;> omega
  have hNV := (normalizer_eq_of_hyp121 h1001 h331 hyp).2
  have hr := le_rParam hyp hβ hNV hone
  have hm := mParam_eq_two hyp hβ hV
  refine ⟨hr, ?_, hm⟩
  unfold sParam
  rw [← autI_normalizer_eq_top hV, hNV, hm]
  have h2 : ((2 : ℕ) : ℕ∞) ≤ rParam V := le_trans (by exact_mod_cast hn2) hr
  rw [min_eq_right h2]
  rfl

end CFSG.Quasithin.H13
