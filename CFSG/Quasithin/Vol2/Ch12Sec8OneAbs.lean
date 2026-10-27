module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabBasic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace L128A

variable {G : Type} [Group G]

abbrev uA (V V₁ : Subgroup G) : Subgroup G := conjClosure V (Subgroup.normalizer (V₁ : Set G))

abbrev wA (V V₁ : Subgroup G) : Subgroup G := uA V V₁ ⊓ Subgroup.centralizer (V : Set G)

structure Setting (V V₁ L T : Subgroup G) : Prop where
  hyp : AlmostSpecialL2Hyp 1 V V₁ L T (Subgroup.normalizer (V₁ : Set G))
  card_V : Nat.card V = 4
  card_V₁ : Nat.card V₁ = 2
  centralizer : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T)
  sThree : Nonempty (OTwoQuot (L ⊔ T) ≃* Equiv.Perm (Fin 3))
  inf_centerOf : V ⊓ centerOf (uA V V₁) = V₁

structure Good (V₁ L : Subgroup G) (g : G) : Prop where
  mem : g ∈ L
  not_mem : g ∉ Subgroup.normalizer (V₁ : Set G)

theorem le_uA (V V₁ : Subgroup G) : V ≤ uA V V₁ := le_conjClosure _ _

theorem wA_le_uA (V V₁ : Subgroup G) : wA V V₁ ≤ uA V V₁ := inf_le_left

theorem normalizer_le_normalizer_uA (V V₁ : Subgroup G) :
    Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (uA V V₁ : Set G) :=
  le_normalizer_conjClosure _ _

theorem centerOf_uA_le_wA (V V₁ : Subgroup G) : centerOf (uA V V₁) ≤ wA V V₁ :=
  le_inf inf_le_left (fun _ hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
    (Subgroup.mem_centralizer_iff.mp hx.2) y (le_uA V V₁ hy))

theorem Good.mem_sup {V₁ L : Subgroup G} {g : G} (hg : Good V₁ L g) (U : Subgroup G) :
    g ∈ L ⊔ U :=
  Subgroup.mem_sup_left hg.mem

theorem Good.mem_normalizer_pCoreOf {V₁ L : Subgroup G} {g : G} (hg : Good V₁ L g)
    (U : Subgroup G) : g ∈ Subgroup.normalizer (pCoreOf 2 (L ⊔ U) : Set G) :=
  le_normalizer_pCoreOf 2 _ (hg.mem_sup U)

namespace Setting

variable [Finite G] {V V₁ L T : Subgroup G}

omit [Finite G] in
theorem base (S : Setting V V₁ L T) :
    AlmostSpecialHyp V V₁ L T (Subgroup.normalizer (V₁ : Set G)) :=
  S.hyp.base

omit [Finite G] in
theorem normalizer_eq_centralizer (S : Setting V V₁ L T) :
    Subgroup.normalizer (V₁ : Set G) = Subgroup.centralizer (V₁ : Set G) :=
  le_antisymm (normalizer_le_centralizer_of_card_two S.card_V₁)
    (Subgroup.centralizer_le_normalizer _)

omit [Finite G] in
theorem V₁_le (S : Setting V V₁ L T) : V₁ ≤ V := S.base.le_V

theorem uA_le_T (S : Setting V V₁ L T) : uA V V₁ ≤ T := S.base.G22_three.1

theorem T_le_normalizer_uA (S : Setting V V₁ L T) :
    T ≤ Subgroup.normalizer (uA V V₁ : Set G) :=
  S.base.G22_three.2

omit [Finite G] in
theorem uA_le_normalizer (S : Setting V V₁ L T) :
    uA V V₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
  S.base.conjClosure_le_N

omit [Finite G] in
theorem uA_le_centralizer (S : Setting V V₁ L T) :
    uA V V₁ ≤ Subgroup.centralizer (V₁ : Set G) := by
  rw [← S.normalizer_eq_centralizer]
  exact S.uA_le_normalizer

theorem commutator_mem (S : Setting V V₁ L T) {x y : G} (hx : x ∈ uA V V₁) (hy : y ∈ uA V V₁) :
    x * y * x⁻¹ * y⁻¹ ∈ V₁ :=
  S.base.G22_commutator_mem hx hy

theorem sq_mem (S : Setting V V₁ L T) {x : G} (hx : x ∈ uA V V₁) : x ^ 2 ∈ V₁ :=
  S.base.G22_sq_mem hx

omit [Finite G] in
theorem V₁_le_centerOf (S : Setting V V₁ L T) : V₁ ≤ centerOf (uA V V₁) := by
  refine le_inf (S.V₁_le.trans (le_uA V V₁)) ?_
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact ((Subgroup.mem_centralizer_iff.mp (S.uA_le_centralizer hu)) z hz).symm

theorem commutator_mem_centerOf (S : Setting V V₁ L T) :
    ∀ a ∈ uA V V₁, ∀ b ∈ uA V V₁, a * b * a⁻¹ * b⁻¹ ∈ centerOf (uA V V₁) :=
  fun _ ha _ hb => S.V₁_le_centerOf (S.commutator_mem ha hb)

omit [Finite G] in
theorem exists_gen (S : Setting V V₁ L T) :
    ∃ z : G, z ∈ V₁ ∧ z ≠ 1 ∧ ∀ w ∈ V₁, w = 1 ∨ w = z := by
  obtain ⟨y, hy1, hy⟩ := (Nat.card_eq_two_iff' (1 : V₁)).mp S.card_V₁
  refine ⟨y, y.2, fun he => hy1 (Subtype.ext he), fun w hw => ?_⟩
  by_cases hw1 : w = 1
  · exact Or.inl hw1
  · exact Or.inr (congrArg Subtype.val (hy ⟨w, hw⟩ fun he => hw1 (congrArg Subtype.val he)))

theorem exists_mem_not_mem (S : Setting V V₁ L T) : ∃ a ∈ V, a ∉ V₁ := by
  by_contra hall
  push Not at hall
  have := Subgroup.card_le_of_le (show V ≤ V₁ from fun a ha => hall a ha)
  rw [S.card_V, S.card_V₁] at this
  omega

theorem V_cases (S : Setting V V₁ L T) {z a : G} (hzV₁ : z ∈ V₁) (hz1 : z ≠ 1) (ha : a ∈ V)
    (haV₁ : a ∉ V₁) : ∀ w ∈ V, w = 1 ∨ w = z ∨ w = a ∨ w = z * a := by
  have hzV : z ∈ V := S.V₁_le hzV₁
  have hsq : z * z = 1 := by simpa [sq] using S.base.sq_eq_one_of_mem_V hzV
  have ha1 : a ≠ 1 := fun he => haV₁ (he ▸ Subgroup.one_mem _)
  have haz : a ≠ z := fun he => haV₁ (he ▸ hzV₁)
  have hza1 : z * a ≠ 1 := by
    intro he
    apply haV₁
    have : a = z⁻¹ := by
      calc a = z⁻¹ * (z * a) := by group
        _ = z⁻¹ := by rw [he, mul_one]
    rw [this, inv_eq_of_mul_eq_one_right hsq]
    exact hzV₁
  have hzaz : z * a ≠ z := fun he => ha1 (by simpa using he)
  have hzaa : z * a ≠ a := fun he => hz1 (by simpa using he)
  intro w hw
  have := eq_or_eq_or_eq_or_eq_of_card_four S.card_V
    (a := (1 : V)) (b := ⟨z, hzV⟩) (c := ⟨a, ha⟩) (d := ⟨z * a, Subgroup.mul_mem _ hzV ha⟩)
    (fun he => hz1 (congrArg Subtype.val he).symm)
    (fun he => ha1 (congrArg Subtype.val he).symm)
    (fun he => hza1 (congrArg Subtype.val he).symm)
    (fun he => haz (congrArg Subtype.val he).symm)
    (fun he => hzaz (congrArg Subtype.val he).symm)
    (fun he => hzaa (congrArg Subtype.val he).symm) ⟨w, hw⟩
  rcases this with he | he | he | he
  · exact Or.inl (congrArg Subtype.val he)
  · exact Or.inr (Or.inl (congrArg Subtype.val he))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val he)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val he)))

omit [Finite G] in
theorem L_le_normalizer_V (S : Setting V V₁ L T) : L ≤ Subgroup.normalizer (V : Set G) := by
  obtain ⟨hnorm, -⟩ := S.hyp.natural
  exact hnorm

omit [Finite G] in
theorem LT_le_normalizer_V (S : Setting V V₁ L T) : L ⊔ T ≤ Subgroup.normalizer (V : Set G) :=
  sup_le S.L_le_normalizer_V S.base.T_le_normV

theorem uA_le_normalizer_V (S : Setting V V₁ L T) : uA V V₁ ≤ Subgroup.normalizer (V : Set G) :=
  S.uA_le_T.trans S.base.T_le_normV

omit [Finite G] in
theorem card_OTwoQuot (S : Setting V V₁ L T) : Nat.card (OTwoQuot (L ⊔ T)) = 6 := by
  obtain ⟨e⟩ := S.sThree
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

omit [Finite G] in
theorem card_autOn_LT (S : Setting V V₁ L T) : Nat.card (autOn (L ⊔ T) V) = 6 := by
  rw [card_autOn_eq_relIndex S.LT_le_normalizer_V, S.centralizer]
  have hsub : (pCoreOf 2 (L ⊔ T)).subgroupOf (L ⊔ T) = CFSG.Open.pCore 2 ↥(L ⊔ T) :=
    map_subtype_subgroupOf' (CFSG.Open.pCore 2 ↥(L ⊔ T))
  show ((pCoreOf 2 (L ⊔ T)).subgroupOf (L ⊔ T)).index = 6
  rw [hsub]
  exact S.card_OTwoQuot

theorem autOn_LT_eq_top (S : Setting V V₁ L T) : autOn (L ⊔ T) V = ⊤ := by
  obtain ⟨hcard, hfin⟩ := card_mulAut_le_six_of_card_four (V := ↥V) S.card_V
  have h6 := S.card_autOn_LT
  have := hfin
  have hle := Subgroup.card_le_card_group (autOn (L ⊔ T) V)
  exact Subgroup.eq_top_of_card_eq _ (by omega)

theorem conj_eq_of_not_centralizes (S : Setting V V₁ L T) {z a x : G} (hzV₁ : z ∈ V₁)
    (hz1 : z ≠ 1) (haV : a ∈ V) (haV₁ : a ∉ V₁) (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hxZ : x ∈ Subgroup.centralizer (V₁ : Set G))
    (hxC : x ∉ Subgroup.centralizer (V : Set G)) : x * a * x⁻¹ = z * a := by
  have hcases := S.V_cases hzV₁ hz1 haV haV₁
  have hxz : x * z * x⁻¹ = z := by
    have := (Subgroup.mem_centralizer_iff.mp hxZ) z hzV₁
    rw [← this]
    group
  have hxaV : x * a * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hx a).mp haV
  have ha1 : a ≠ 1 := fun he => haV₁ (he ▸ Subgroup.one_mem _)
  rcases hcases _ hxaV with he | he | he | he
  · exfalso
    apply ha1
    have : a = x⁻¹ * (x * a * x⁻¹) * x := by group
    rw [this, he]
    group
  · exfalso
    apply haV₁
    have : a = x⁻¹ * (x * a * x⁻¹) * x := by group
    rw [this, he, ← hxz]
    have e : x⁻¹ * (x * z * x⁻¹) * x = z := by group
    rw [e]
    exact hzV₁
  · exfalso
    apply hxC
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rcases hcases w hw with e | e | e | e <;> rw [e]
    · simp
    · calc z * x = (x * z * x⁻¹) * x := by rw [hxz]
        _ = x * z := by group
    · calc a * x = (x * a * x⁻¹) * x := by rw [he]
        _ = x * a := by group
    · have h1 : x * (z * a) * x⁻¹ = z * a := by
        have : x * (z * a) * x⁻¹ = (x * z * x⁻¹) * (x * a * x⁻¹) := by group
        rw [this, hxz, he]
      calc z * a * x = (x * (z * a) * x⁻¹) * x := by rw [h1]
        _ = x * (z * a) := by group
  · exact he

theorem inv_mul_mem_centralizer_V (S : Setting V V₁ L T) {u u' : G}
    (hu : u ∈ Subgroup.normalizer (V : Set G)) (hu' : u' ∈ Subgroup.normalizer (V : Set G))
    (huZ : u ∈ Subgroup.centralizer (V₁ : Set G)) (hu'Z : u' ∈ Subgroup.centralizer (V₁ : Set G))
    (hnu : u ∉ Subgroup.centralizer (V : Set G)) (hnu' : u' ∉ Subgroup.centralizer (V : Set G)) :
    u⁻¹ * u' ∈ Subgroup.centralizer (V : Set G) := by
  obtain ⟨z, hzV₁, hz1, -⟩ := S.exists_gen
  obtain ⟨a, haV, haV₁⟩ := S.exists_mem_not_mem
  have hcases := S.V_cases hzV₁ hz1 haV haV₁
  have hzV := S.V₁_le hzV₁
  have hsq : z * z = 1 := by simpa [sq] using S.base.sq_eq_one_of_mem_V hzV
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hsq
  have e1 := S.conj_eq_of_not_centralizes hzV₁ hz1 haV haV₁ hu huZ hnu
  have e2 := S.conj_eq_of_not_centralizes hzV₁ hz1 haV haV₁ hu' hu'Z hnu'
  have huz : u⁻¹ * z * u = z := by
    have := (Subgroup.mem_centralizer_iff.mp huZ) z hzV₁
    calc u⁻¹ * z * u = u⁻¹ * (z * u) := by group
      _ = u⁻¹ * (u * z) := by rw [this]
      _ = z := by group
  have hua : u⁻¹ * a * u = z * a := by
    have h1 : a = (u⁻¹ * z * u) * (u⁻¹ * a * u) := by
      calc a = u⁻¹ * (u * a * u⁻¹) * u := by group
        _ = u⁻¹ * (z * a) * u := by rw [e1]
        _ = (u⁻¹ * z * u) * (u⁻¹ * a * u) := by group
    rw [huz] at h1
    calc u⁻¹ * a * u = z⁻¹ * (z * (u⁻¹ * a * u)) := by group
      _ = z⁻¹ * a := by rw [← h1]
      _ = z * a := by rw [hzi]
  have hfixa : (u⁻¹ * u') * a * (u⁻¹ * u')⁻¹ = a := by
    calc (u⁻¹ * u') * a * (u⁻¹ * u')⁻¹ = u⁻¹ * (u' * a * u'⁻¹) * u := by group
      _ = u⁻¹ * (z * a) * u := by rw [e2]
      _ = (u⁻¹ * z * u) * (u⁻¹ * a * u) := by group
      _ = z * (z * a) := by rw [huz, hua]
      _ = (z * z) * a := by group
      _ = a := by rw [hsq, one_mul]
  have hfixz : (u⁻¹ * u') * z * (u⁻¹ * u')⁻¹ = z := by
    have h2 := (Subgroup.mem_centralizer_iff.mp hu'Z) z hzV₁
    calc (u⁻¹ * u') * z * (u⁻¹ * u')⁻¹ = u⁻¹ * (u' * z * u'⁻¹) * u := by group
      _ = u⁻¹ * z * u := by rw [← h2]; group
      _ = z := huz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  set c := u⁻¹ * u' with hc
  rcases hcases w hw with e | e | e | e <;> rw [e]
  · simp
  · calc z * c = (c * z * c⁻¹) * c := by rw [hfixz]
      _ = c * z := by group
  · calc a * c = (c * a * c⁻¹) * c := by rw [hfixa]
      _ = c * a := by group
  · have : c * (z * a) * c⁻¹ = z * a := by
      have : c * (z * a) * c⁻¹ = (c * z * c⁻¹) * (c * a * c⁻¹) := by group
      rw [this, hfixz, hfixa]
    calc z * a * c = (c * (z * a) * c⁻¹) * c := by rw [this]
      _ = c * (z * a) := by group

theorem not_le_centralizer_V (S : Setting V V₁ L T) :
    ¬ uA V V₁ ≤ Subgroup.centralizer (V : Set G) := by
  intro hc
  have hVZ : V ≤ V ⊓ centerOf (uA V V₁) := le_inf le_rfl (le_inf (le_uA V V₁) fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun u hu =>
      ((Subgroup.mem_centralizer_iff.mp (hc hu)) v hv).symm)
  rw [S.inf_centerOf] at hVZ
  have := Subgroup.card_le_of_le hVZ
  rw [S.card_V, S.card_V₁] at this
  omega

theorem not_isMulCommutative (S : Setting V V₁ L T) : ¬ IsMulCommutative ↥(uA V V₁) := by
  intro hU
  apply S.not_le_centralizer_V
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact congrArg Subtype.val (hU.is_comm.comm (⟨v, le_uA V V₁ hv⟩ : uA V V₁) ⟨u, hu⟩)

theorem commutator_uA_eq (S : Setting V V₁ L T) : ⁅uA V V₁, uA V V₁⁆ = V₁ := by
  have hle : ⁅uA V V₁, uA V V₁⁆ ≤ V₁ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact S.commutator_mem ha hb
  by_cases hbot : ⁅uA V V₁, uA V V₁⁆ = ⊥
  · exfalso
    apply S.not_isMulCommutative
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨x, hx⟩ := a
    obtain ⟨y, hy⟩ := b
    refine Subtype.ext ?_
    show x * y = y * x
    have : ⁅x, y⁆ ∈ ⁅uA V V₁, uA V V₁⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [hbot, Subgroup.mem_bot, commutatorElement_def] at this
    calc x * y = (x * y * x⁻¹ * y⁻¹) * y * x := by group
      _ = y * x := by rw [this]; group
  · have hcard : Nat.card ↥⁅uA V V₁, uA V V₁⁆ ∣ 2 := by
      rw [← S.card_V₁]
      exact Subgroup.card_dvd_of_le hle
    have h1 : Nat.card ↥⁅uA V V₁, uA V V₁⁆ ≠ 1 := fun h1 => hbot (Subgroup.card_eq_one.mp h1)
    have h2 : Nat.card ↥⁅uA V V₁, uA V V₁⁆ = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hcard with h | h
      · exact absurd h h1
      · exact h
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [h2, S.card_V₁])

omit [Finite G] in
theorem le_wA (S : Setting V V₁ L T) : V ≤ wA V V₁ :=
  le_inf (le_uA V V₁) fun _ hx => Subgroup.mem_centralizer_iff.mpr fun _ hy =>
    S.base.commV hy hx

theorem uA_le_normalizer_wA (S : Setting V V₁ L T) :
    uA V V₁ ≤ Subgroup.normalizer (wA V V₁ : Set G) := by
  intro u hu
  have h1 : u ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
    normalizer_le_normalizer_centralizer'' _ (S.uA_le_normalizer_V hu)
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hu, h1⟩

theorem T_le_normalizer_wA (S : Setting V V₁ L T) :
    T ≤ Subgroup.normalizer (wA V V₁ : Set G) := by
  intro t ht
  have h1 : t ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
    normalizer_le_normalizer_centralizer'' _ (S.base.T_le_normV ht)
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨S.T_le_normalizer_uA ht, h1⟩

theorem mem_wA_or_inv_mul_mem (S : Setting V V₁ L T) {u u' : G} (hu : u ∈ uA V V₁)
    (hu' : u' ∈ uA V V₁) (huW : u ∉ wA V V₁) : u' ∈ wA V V₁ ∨ u⁻¹ * u' ∈ wA V V₁ := by
  by_cases hu'W : u' ∈ wA V V₁
  · exact Or.inl hu'W
  · right
    refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hu', ?_⟩
    exact S.inv_mul_mem_centralizer_V (S.uA_le_normalizer_V hu) (S.uA_le_normalizer_V hu')
      (S.uA_le_centralizer hu) (S.uA_le_centralizer hu')
      (fun hc => huW ⟨hu, hc⟩) (fun hc => hu'W ⟨hu', hc⟩)

end Setting

end L128A

end CFSG.Quasithin.H13
