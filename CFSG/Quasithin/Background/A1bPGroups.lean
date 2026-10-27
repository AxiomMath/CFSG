module

public import CFSG.Quasithin.Background.TwoReduced
public import CFSG.LocalAnalysis.SectionRank.Ccomm.RankTwo
public import CFSG.LocalAnalysis.SectionRank.Ccomm.NonabelianCube
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.SectionRank CFSG.SectionRank.Ccomm
open scoped commutatorElement

variable {P : Type*} [Group P]

@[expose] def frattiniIn (X : Subgroup P) : Subgroup P := (frattini X).map X.subtype

@[expose] def ClassLeTwo (X : Subgroup P) : Prop := ⁅⁅X, X⁆, X⁆ = ⊥

structure IsSupercritical (p : ℕ) (X : Subgroup P) : Prop where
  characteristic : X.Characteristic
  frattini_le : frattiniIn X ≤ centerOf X
  commutator_le : ⁅X, (⊤ : Subgroup P)⁆ ≤ centerOf X
  pow_eq_one : ∀ x ∈ X, x ^ p = 1
  mem_of_orderOf_eq : ∀ x ∈ Subgroup.centralizer (X : Set P), orderOf x = p → x ∈ X

@[expose] def IsPOnePlusTwo (p : ℕ) (X : Type*) [Group X] : Prop :=
  CFSG.IsExtraspecial p X ∧ Nat.card X = p ^ 3 ∧ ∀ x : X, x ^ p = 1

@[expose] def IsElemAbelianOfRank (p n : ℕ) (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Multiplicative (Fin n → ZMod p))

theorem mem_ker_frattiniAction_iff (D : Subgroup P) [D.Characteristic] (α : MulAut P) :
    α ∈ (frattiniAction D).ker ↔ ∀ x ∈ D, x⁻¹ * α x ∈ frattiniIn D := by
  rw [mem_ker_frattiniAction]
  constructor
  · intro h x hx
    have := h ⟨x, hx⟩
    exact ⟨_, this, rfl⟩
  · intro h d
    obtain ⟨y, hy, hyd⟩ := h d d.2
    have : y = d⁻¹ * MulAut.characteristic D α d := Subtype.ext (by simpa using hyd)
    rwa [← this]

theorem IsSupercritical.classLeTwo {p : ℕ} {X : Subgroup P} (hX : IsSupercritical p X) :
    ClassLeTwo X := by
  unfold ClassLeTwo
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro a ha b hb
  have ha' : a ∈ centerOf X := hX.commutator_le (Subgroup.commutator_mono le_rfl le_top ha)
  have := Subgroup.mem_centralizer_iff.1 ha'.2 b hb
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact this.symm

section A121

variable {p : ℕ} [hp : Fact p.Prime] [Finite P]

omit [Finite P] in
theorem isSupercritical_bot_of_subsingleton [Subsingleton P] : IsSupercritical p (⊥ : Subgroup P) :=
  { characteristic := inferInstance
    frattini_le := by
      rintro _ ⟨y, -, rfl⟩
      have : (⊥ : Subgroup P).subtype y = 1 := Subsingleton.elim _ _
      rw [this]
      exact Subgroup.one_mem _
    commutator_le := by
      rw [Subgroup.commutator_bot_left]
      exact bot_le
    pow_eq_one := fun x _ => by rw [Subsingleton.elim x 1, one_pow]
    mem_of_orderOf_eq := fun x _ hx => by
      rw [Subsingleton.elim x 1, orderOf_one] at hx
      exact absurd hx.symm hp.out.one_lt.ne' }

theorem isSupercritical_of {D : Subgroup P} (hDc : D.Characteristic) (hDp : ∀ x ∈ D, x ^ p = 1)
    (hDZ : ⁅D, (⊤ : Subgroup P)⁆ ≤ D ⊓ Subgroup.centralizer (D : Set P))
    (hDt : ∀ x ∈ Subgroup.centralizer (D : Set P), orderOf x = p → x ∈ D) :
    IsSupercritical p D := by
  refine ⟨hDc, ?_, hDZ, hDp, hDt⟩
  have hfin : frattini D ≤ Subgroup.center D := by
    refine frattini_le_of_commutator_pow_mem (p := p) (Subgroup.center D) (fun a b => ?_)
      (fun a => ?_)
    · have h1 : ⁅(a : P), (b : P)⁆ ∈ ⁅D, (⊤ : Subgroup P)⁆ :=
        Subgroup.commutator_mem_commutator a.2 (Subgroup.mem_top _)
      have h2 := (hDZ h1).2
      have e : ((⁅a, b⁆ : D) : P) = ⁅(a : P), (b : P)⁆ := map_commutatorElement D.subtype a b
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      change (g : P) * ((⁅a, b⁆ : D) : P) = ((⁅a, b⁆ : D) : P) * (g : P)
      rw [e]
      exact Subgroup.mem_centralizer_iff.1 h2 (g : P) g.2
    · have : a ^ p = 1 := Subtype.ext (by simpa using hDp a a.2)
      rw [this]
      exact Subgroup.one_mem _
  rintro _ ⟨y, hy, rfl⟩
  have hy' := hfin hy
  rw [Subgroup.mem_center_iff] at hy'
  refine ⟨y.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
  exact congrArg Subtype.val (hy' ⟨g, hg⟩)

theorem exists_isSupercritical_faithful (hp2 : p ≠ 2) (hP : IsPGroup p P) :
    ∃ X : Subgroup P, IsSupercritical p X ∧
      ∀ α : MulAut P, (orderOf α).Coprime p → (∀ x ∈ X, x⁻¹ * α x ∈ frattiniIn X) → α = 1 := by
  rcases subsingleton_or_nontrivial P with hsub | hnt
  · exact ⟨⊥, isSupercritical_bot_of_subsingleton, fun α _ _ =>
      MulEquiv.ext fun x => Subsingleton.elim _ _⟩
  · obtain ⟨D, hDc, -, hDp, hDZ, hDt, hker⟩ := supercritical_witness hp2 hP
    refine ⟨D, isSupercritical_of hDc hDp hDZ hDt, fun α hα hfix => ?_⟩
    have hmem : α ∈ (frattiniAction D).ker := (mem_ker_frattiniAction_iff D α).2 hfix
    obtain ⟨k, hk⟩ := hker ⟨α, hmem⟩
    have h1 : α ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : orderOf α ∣ p ^ k := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf α = 1 := Nat.Coprime.eq_one_of_dvd (hα.pow_right k) h2
    exact orderOf_eq_one_iff.1 h3

theorem exists_isSupercritical (hp2 : p ≠ 2) (hP : IsPGroup p P) :
    ∃ X : Subgroup P, IsSupercritical p X :=
  (exists_isSupercritical_faithful hp2 hP).imp fun _ h => h.1

theorem exists_eq_zpowers_of_pRank_le_one (hP : IsPGroup p P) {X : Subgroup P} (hX : X ≠ ⊥)
    (hXp : ∀ x ∈ X, x ^ p = 1) (hr : pRank p X ≤ 1) :
    ∃ z ∈ X, X = Subgroup.zpowers z ∧ orderOf z = p := by
  have hnt : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).2 hX
  have hcn : Nontrivial (Subgroup.center X) := (hP.to_subgroup X).center_nontrivial
  obtain ⟨⟨z', hz'c⟩, hz'1⟩ := exists_ne (1 : Subgroup.center X)
  have hz'1' : z' ≠ 1 := fun h => hz'1 (Subtype.ext h)
  have hz'p : z' ^ p = 1 := Subtype.ext (by simpa using hXp z' z'.2)
  have hord' : orderOf z' = p := orderOf_eq_prime hz'p hz'1'
  have hzord : orderOf (z' : P) = p := by rw [Subgroup.orderOf_coe]; exact hord'
  have hzX : (z' : P) ∈ X := z'.2
  refine ⟨z', hzX, ?_, hzord⟩
  have hle : ∀ y ∈ X, y ∈ Subgroup.zpowers (z' : P) := by
    intro y hy
    have hcomm : ({(z' : P), y} : Set P).Pairwise Commute := by
      rw [Set.pairwise_pair]
      intro _
      have h1 : (⟨y, hy⟩ : X) * z' = z' * ⟨y, hy⟩ := Subgroup.mem_center_iff.1 hz'c ⟨y, hy⟩
      have h2 : y * (z' : P) = (z' : P) * y := congrArg Subtype.val h1
      exact ⟨h2.symm, h2⟩
    have hEc := Subgroup.isMulCommutative_closure hcomm
    have hEX : Subgroup.closure ({(z' : P), y} : Set P) ≤ X := by
      rw [Subgroup.closure_le]
      intro w hw
      rcases hw with rfl | rfl
      · exact hzX
      · exact hy
    have hEel : IsElemAbelian p (Subgroup.closure ({(z' : P), y} : Set P)) :=
      ⟨hEc, fun x hx => hXp x (hEX hx)⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (hP.to_subgroup (Subgroup.closure ({(z' : P), y} :
      Set P)))
    have hk1 : k ≤ 1 := (le_pRank hp.out.one_lt hEX hEel hk).trans hr
    have hcard : Nat.card (Subgroup.closure ({(z' : P), y} : Set P)) ≤ p := by
      rw [hk]
      calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.out.pos hk1
        _ = p := pow_one p
    have hzE : Subgroup.zpowers (z' : P) ≤ Subgroup.closure ({(z' : P), y} : Set P) :=
      Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
    have hzcard : Nat.card (Subgroup.zpowers (z' : P)) = p := by rw [Nat.card_zpowers, hzord]
    have heq := Subgroup.eq_of_le_of_card_ge hzE (by rw [hzcard]; exact hcard)
    rw [heq]
    exact Subgroup.subset_closure (by simp)
  exact le_antisymm (fun y hy => hle y hy) (Subgroup.zpowers_le.2 hzX)

theorem IsSupercritical.one_lt_pRank {X : Subgroup P} (hX : IsSupercritical p X)
    (hP : IsPGroup p P) (h : 1 < pRank p (⊤ : Subgroup P)) : 1 < pRank p X := by
  by_contra hle
  push Not at hle
  have hCtop : Subgroup.centralizer (X : Set P) = ⊤ ∧ Nat.card X ≤ p := by
    rcases eq_or_ne X ⊥ with hbot | hne
    · subst hbot
      refine ⟨?_, ?_⟩
      · rw [eq_top_iff]
        intro g _
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hh
        rw [hh, one_mul, mul_one]
      · rw [Subgroup.card_bot]
        exact hp.out.one_lt.le
    · obtain ⟨z, hzX, hXz, hzord⟩ := exists_eq_zpowers_of_pRank_le_one hP hne hX.pow_eq_one hle
      have hcardX : Nat.card X = p := by rw [hXz, Nat.card_zpowers, hzord]
      have hcentral : ∀ g : P, ∀ x ∈ X, g * x * g⁻¹ = x := by
        have := hX.characteristic
        let _ : MulAction P X := MulAction.compHom X (MulAut.conjNormal : P →* MulAut X)
        have hmod := hP.card_modEq_card_fixedPoints X
        rw [hcardX] at hmod
        have hdvd : p ∣ Nat.card (MulAction.fixedPoints P X) :=
          (Nat.modEq_zero_iff_dvd).1 (hmod.symm.trans ((Nat.modEq_zero_iff_dvd).2 dvd_rfl))
        have hne1 : Nat.card (MulAction.fixedPoints P X) ≠ 0 := by
          have : Nonempty (MulAction.fixedPoints P X) := ⟨⟨1, fun g => by
            change MulAut.conjNormal g (1 : X) = 1
            exact map_one _⟩⟩
          exact Nat.card_pos.ne'
        have hge : p ≤ Nat.card (MulAction.fixedPoints P X) :=
          Nat.le_of_dvd (Nat.pos_of_ne_zero hne1) hdvd
        have hbij : Function.Bijective (Subtype.val : MulAction.fixedPoints P X → X) :=
          Function.Injective.bijective_of_nat_card_le Subtype.val_injective (by
            rw [hcardX]; exact hge)
        intro g x hx
        obtain ⟨⟨w, hw⟩, hwx⟩ := hbij.2 ⟨x, hx⟩
        have h1 : g • (⟨x, hx⟩ : X) = ⟨x, hx⟩ := by
          rw [← hwx]
          exact hw g
        have h2 := congrArg Subtype.val h1
        rwa [show ((g • (⟨x, hx⟩ : X) : X) : P) = g * x * g⁻¹ from
          MulAut.conjNormal_apply g ⟨x, hx⟩] at h2
      refine ⟨?_, hcardX.le⟩
      rw [eq_top_iff]
      intro g _
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (mul_inv_eq_iff_eq_mul.1 (hcentral g x hx)).symm
  obtain ⟨hCtop, hXcard⟩ := hCtop
  have hrank : pRank p (⊤ : Subgroup P) ≤ 1 := by
    refine pRank_le hp.out.one_lt (k := 1) fun E _ hE => ?_
    have hEX : E ≤ X := by
      intro e he
      by_cases he1 : e = 1
      · rw [he1]
        exact X.one_mem
      · have hep : e ^ p = 1 := hE.2 e he
        have hord : orderOf e = p := orderOf_eq_prime hep he1
        refine hX.mem_of_orderOf_eq e ?_ hord
        rw [hCtop]
        exact Subgroup.mem_top e
    calc Nat.card E ≤ Nat.card X := Subgroup.card_le_of_le hEX
      _ ≤ p := hXcard
      _ = p ^ 1 := (pow_one p).symm
  omega

end A121

section A124

variable {p : ℕ} [hp : Fact p.Prime] [Finite P]

omit [Finite P] in
theorem pow_eq_one_of_classLeTwo (hp2 : p ≠ 2) (hcl : ClassLeTwo (⊤ : Subgroup P))
    (hgen : Subgroup.closure {x : P | x ^ p = 1} = ⊤) : ∀ x : P, x ^ p = 1 := by
  have hcen : ∀ x y z : P, Commute z ⁅x, y⁆ := by
    intro x y z
    have h : ⁅⁅x, y⁆, z⁆ ∈ ⁅⁅(⊤ : Subgroup P), ⊤⁆, ⊤⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.commutator_mem_commutator
        (Subgroup.mem_top x) (Subgroup.mem_top y)) (Subgroup.mem_top z)
    rw [hcl, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact h.symm
  let T : Subgroup P :=
    { carrier := {x | x ^ p = 1}
      mul_mem' := fun {x y} hx hy => by
        have hc : ⁅y, x⁆ ^ p = 1 := by
          have := commutatorElement_pow_left (hcen y x y) p
          rw [show y ^ p = 1 from hy, commutatorElement_one_left] at this
          exact this.symm
        change (x * y) ^ p = 1
        rw [mul_pow_prime_eq_of_commute hp.out hp2 (hcen y x x) (hcen y x y) hc]
        rw [show x ^ p = 1 from hx, show y ^ p = 1 from hy, one_mul]
      one_mem' := one_pow p
      inv_mem' := fun {x} hx => by
        change x⁻¹ ^ p = 1
        rw [inv_pow, show x ^ p = 1 from hx, inv_one] }
  have hT : T = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    exact fun x hx => hx
  intro x
  have : x ∈ T := hT ▸ Subgroup.mem_top x
  exact this

theorem commutative_of_card_le_prime_sq (hP : IsPGroup p P) (hle : Nat.card P ≤ p ^ 2) :
    ∀ a b : P, a * b = b * a := by
  obtain ⟨r, hr⟩ := hP.exists_card_eq
  have hr2 : r ≤ 2 := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 (hr ▸ hle)
  interval_cases r
  · have : Subsingleton P := Finite.card_le_one_iff_subsingleton.1 (by simp [hr])
    exact fun a b => Subsingleton.elim _ _
  · have : IsCyclic P := isCyclic_of_prime_card (by simpa using hr)
    exact fun a b => mul_comm' a b
  · have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hr
    exact fun a b => mul_comm' a b

theorem isElemAbelianOfRank_two_or_isPOnePlusTwo (hp2 : p ≠ 2) (hP : IsPGroup p P)
    (hΩ : Subgroup.closure {x : P | x ^ p = 1} = ⊤) (hrank : pRank p (⊤ : Subgroup P) = 2)
    (hcl : ClassLeTwo (⊤ : Subgroup P)) :
    IsElemAbelianOfRank p 2 P ∨ IsPOnePlusTwo p P := by
  have hexp := pow_eq_one_of_classLeTwo hp2 hcl hΩ
  obtain ⟨hcard3, -⟩ := rank_two_exponent_prime_order_bound hP hexp hrank.le
  by_cases hcomm : ∀ a b : P, a * b = b * a
  · left
    obtain ⟨r, hr⟩ := hP.exists_card_eq
    have hel : IsElemAbelian p (⊤ : Subgroup P) :=
      ⟨⟨⟨fun a b => Subtype.ext (hcomm _ _)⟩⟩, fun x _ => hexp x⟩
    have hr' : Nat.card (⊤ : Subgroup P) = p ^ r := by rw [Subgroup.card_top, hr]
    have hr2 : r ≤ 2 := hrank ▸ le_pRank hp.out.one_lt le_rfl hel hr'
    obtain ⟨E, -, hEel, hEcard⟩ := exists_pRank hp.out.one_lt (⊤ : Subgroup P)
    rw [hrank] at hEcard
    have hEle : Nat.card E ≤ Nat.card P := by
      rw [← Subgroup.card_top (G := P)]
      exact Subgroup.card_le_of_le le_top
    have h2r : 2 ≤ r := by
      rw [hEcard, hr] at hEle
      exact (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hEle
    have hr2' : r = 2 := le_antisymm hr2 h2r
    exact nonempty_mulEquiv_of_elementary hcomm hexp (hr2' ▸ hr)
  · right
    have hnotle : ¬ Nat.card P ≤ p ^ 2 := fun h => hcomm (commutative_of_card_le_prime_sq hP h)
    obtain ⟨r, hr⟩ := hP.exists_card_eq
    have hr3 : r = 3 := by
      have h1 : r ≤ 3 := (Nat.pow_le_pow_iff_right hp.out.one_lt).1 (hr ▸ hcard3)
      have h2 : ¬ r ≤ 2 := fun h => hnotle (hr ▸ Nat.pow_le_pow_right hp.out.pos h)
      omega
    have hcard : Nat.card P = p ^ 3 := hr3 ▸ hr
    have hnc : ∃ a b : P, a * b ≠ b * a := by
      push Not at hcomm
      exact hcomm
    obtain ⟨-, hcen, hcomQ, hpowQ, hcardQ, -⟩ := nonabelian_prime_cube_central_structure hcard hnc
    refine ⟨?_, hcard, hexp⟩
    refine ⟨hcen, ?_, ?_⟩
    · exact { toIsMulCommutative := ⟨⟨hcomQ⟩⟩
              exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hpowQ }
    · rw [← Finite.one_lt_card_iff_nontrivial, hcardQ]
      exact Nat.one_lt_pow (by norm_num) hp.out.one_lt

end A124

section A125

variable {p : ℕ} [hp : Fact p.Prime] [Finite P]

theorem pRank_top_subtype (X : Subgroup P) : pRank p (⊤ : Subgroup X) = pRank p X := by
  have hp1 := hp.out.one_lt
  apply le_antisymm
  · have h := pRank_le_map hp1 X.subtype X.subtype_injective (⊤ : Subgroup X)
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  · obtain ⟨E, hEX, hE, hcard⟩ := exists_pRank hp1 X
    have hEc : IsMulCommutative E := hE.1
    refine le_pRank hp1 (le_top : E.subgroupOf X ≤ ⊤) ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩ ?_
    · have := mul_comm' (⟨(a : P), a.2⟩ : E) (⟨(b : P), b.2⟩ : E)
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val this
    · apply Subtype.ext
      have := hE.2 (x : P) hx
      simpa using this
    · rw [← hcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv

omit [Finite P] in
theorem classLeTwo_top_of {X : Subgroup P} (hX : ClassLeTwo X) : ClassLeTwo (⊤ : Subgroup X) := by
  unfold ClassLeTwo at *
  have htop : (⊤ : Subgroup X).map X.subtype = X := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have e : Subgroup.map X.subtype ⁅⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆, (⊤ : Subgroup X)⁆ =
      ⁅⁅X, X⁆, X⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator, htop]
  rw [hX] at e
  exact (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).1 e

theorem IsSupercritical.ne_bot [Nontrivial P] {X : Subgroup P} (hX : IsSupercritical p X)
    (hP : IsPGroup p P) : X ≠ ⊥ := by
  intro hbot
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := P) p
    (by obtain ⟨n, hn0, hn⟩ := hP.nontrivial_iff_card.1 inferInstance
        rw [hn]; exact dvd_pow_self p hn0.ne')
  have hmem : e ∈ X := by
    refine hX.mem_of_orderOf_eq e ?_ he
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [hbot, Subgroup.coe_bot, Set.mem_singleton_iff] at hh
    rw [hh, one_mul, mul_one]
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [hmem, orderOf_one] at he
  exact hp.out.one_lt.ne he

theorem one_le_pRank_of_ne_bot {X : Subgroup P} (hX : X ≠ ⊥) (hXp : ∀ x ∈ X, x ^ p = 1) :
    1 ≤ pRank p X := by
  have hp1 := hp.out.one_lt
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hX
  have hap : (a : P) ^ p = 1 := hXp a a.2
  have ha1 : (a : P) ≠ 1 := fun h => ha (Subtype.ext h)
  have hord : orderOf (a : P) = p := orderOf_eq_prime hap ha1
  have hle : Subgroup.zpowers (a : P) ≤ X := Subgroup.zpowers_le.2 a.2
  have hel : IsElemAbelian p (Subgroup.zpowers (a : P)) :=
    ⟨inferInstance, fun y hy => hXp y (hle hy)⟩
  have hcard : Nat.card (Subgroup.zpowers (a : P)) = p ^ 1 := by
    rw [Nat.card_zpowers, hord, pow_one]
  exact le_pRank hp1 hle hel hcard

theorem IsSupercritical.pRank_eq {X : Subgroup P} (hX : IsSupercritical p X)
    (hP : IsPGroup p P) (hr : pRank p (⊤ : Subgroup P) ≤ 2) :
    pRank p X = pRank p (⊤ : Subgroup P) := by
  have hp1 := hp.out.one_lt
  apply le_antisymm (pRank_mono hp1 le_top)
  have h012 : pRank p (⊤ : Subgroup P) = 0 ∨ pRank p (⊤ : Subgroup P) = 1 ∨
      pRank p (⊤ : Subgroup P) = 2 := by omega
  rcases h012 with h0 | h1 | h2
  · rw [h0]
    exact Nat.zero_le _
  · rw [h1]
    have hnt : Nontrivial P := by
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      obtain ⟨E, -, -, hE⟩ := exists_pRank hp1 (⊤ : Subgroup P)
      rw [h1] at hE
      have : Nat.card E ≤ 1 := Finite.card_le_one_iff_subsingleton.2 inferInstance
      rw [hE] at this
      exact absurd (this.trans_lt' (by simpa using hp1)) (lt_irrefl _)
    exact one_le_pRank_of_ne_bot (hX.ne_bot hP) hX.pow_eq_one
  · have := hX.one_lt_pRank hP (by omega)
    have h3 := pRank_mono hp1 (le_top : X ≤ ⊤)
    omega

theorem IsSupercritical.iso_cases (hp2 : p ≠ 2) [Nontrivial P] {X : Subgroup P}
    (hX : IsSupercritical p X) (hP : IsPGroup p P) (hr : pRank p (⊤ : Subgroup P) ≤ 2) :
    Nonempty (X ≃* Multiplicative (ZMod p)) ∨ IsElemAbelianOfRank p 2 X ∨ IsPOnePlusTwo p X := by
  have hXne := hX.ne_bot hP
  have hrk := hX.pRank_eq hP hr
  have hX2 : pRank p X ≤ 2 := hrk ▸ hr
  have hge1 : 1 ≤ pRank p X := one_le_pRank_of_ne_bot hXne hX.pow_eq_one
  by_cases hone : pRank p X ≤ 1
  · left
    obtain ⟨z, hzX, hXz, hzord⟩ := exists_eq_zpowers_of_pRank_le_one hP hXne hX.pow_eq_one hone
    have hcardX : Nat.card X = p := by rw [hXz, Nat.card_zpowers, hzord]
    have hcyc : IsCyclic X := isCyclic_of_prime_card hcardX
    exact ⟨(zmodCyclicMulEquiv hcyc).symm.trans
      (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hcardX).toAddEquiv)⟩
  · have h2 : pRank p X = 2 := by omega
    have hXp : IsPGroup p X := hP.to_subgroup X
    have hΩ : Subgroup.closure {x : X | x ^ p = 1} = ⊤ :=
      eq_top_iff.2 fun x _ => Subgroup.subset_closure
        (Subtype.ext (by simpa using hX.pow_eq_one x x.2))
    exact Or.inr (isElemAbelianOfRank_two_or_isPOnePlusTwo hp2 hXp hΩ
      (by rw [pRank_top_subtype]; exact h2) (classLeTwo_top_of hX.classLeTwo))

theorem exists_injective_GL_le_two {R : Type*} [CommRing R] [Nontrivial R] {m : ℕ} (hm : m ≤ 2) :
    ∃ ι : GL (Fin m) R →* GL (Fin 2) R, Function.Injective ι := by
  interval_cases m
  · refine ⟨1, fun A B _ => ?_⟩
    exact Units.ext (Matrix.ext fun i => i.elim0)
  · refine ⟨(Units.map (Matrix.scalar (Fin 2) : R →+* Matrix (Fin 2) (Fin 2) R).toMonoidHom).comp
      Matrix.GeneralLinearGroup.det, fun A B h => ?_⟩
    have h1 : (Matrix.scalar (Fin 2) (Matrix.det (A : Matrix (Fin 1) (Fin 1) R)) :
        Matrix (Fin 2) (Fin 2) R) =
        Matrix.scalar (Fin 2) (Matrix.det (B : Matrix (Fin 1) (Fin 1) R)) := by
      have := congrArg (fun U : GL (Fin 2) R => (U : Matrix (Fin 2) (Fin 2) R)) h
      simpa using this
    have h2 := congrFun (congrFun h1 0) 0
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h2
    apply Units.ext
    ext i j
    fin_cases i
    fin_cases j
    simpa [Matrix.det_unique] using h2
  · exact ⟨MonoidHom.id _, fun A B h => h⟩

omit [Finite P] in
theorem exists_hom_ker_eq_pCore {A H : Type*} [Group A] [Finite A] [Group H] [Finite H]
    (ρ : A →* H) (hker : IsPGroup p ρ.ker) (hH : ∀ k : ℕ, p ^ k ∣ Nat.card H → k ≤ 1) :
    ∃ ψ : A →* H, ψ.ker = pCore p A := by
  have hN : (pCore p A).Normal := CFSG.LieType.BorelTits.pCore_normal p
  have hkerN : ρ.ker ≤ pCore p A := CFSG.LieType.BorelTits.le_pCore p ρ.normal_ker hker
  by_cases hU1 : (pCore p A).map ρ = ⊥
  · refine ⟨ρ, le_antisymm hkerN fun n hn => ?_⟩
    have : ρ n ∈ (pCore p A).map ρ := Subgroup.mem_map_of_mem ρ hn
    rw [hU1, Subgroup.mem_bot] at this
    exact this
  · set ρ' : A →* ρ.range := ρ.rangeRestrict with hρ'
    have hρ's : Function.Surjective ρ' := ρ.rangeRestrict_surjective
    set U' : Subgroup ρ.range := (pCore p A).map ρ' with hU'
    have : U'.Normal := Subgroup.Normal.map hN ρ' hρ's
    have hU'p : IsPGroup p U' := (CFSG.LieType.BorelTits.pCore_isPGroup p).map ρ'
    have hU'ne : U' ≠ ⊥ := by
      intro h
      apply hU1
      have : (pCore p A).map ρ = (U'.map ρ.range.subtype) := by
        rw [hU', Subgroup.map_map]
        rfl
      rw [this, h, Subgroup.map_bot]
    obtain ⟨a, ha⟩ := hU'p.exists_card_eq
    have ha1 : a = 1 := by
      have hdvd : p ^ a ∣ Nat.card H :=
        ha ▸ (Subgroup.card_subgroup_dvd_card U').trans (Subgroup.card_subgroup_dvd_card ρ.range)
      have hle := hH a hdvd
      have hne : a ≠ 0 := by
        rintro rfl
        rw [pow_zero, Subgroup.card_eq_one] at ha
        exact hU'ne ha
      omega
    have hcardU' : Nat.card U' = p := by rw [ha, ha1, pow_one]
    have hindex : ¬ p ∣ U'.index := by
      intro hdvd
      have h1 : p ^ 2 ∣ Nat.card ρ.range := by
        rw [← U'.card_mul_index, hcardU', pow_two]
        exact mul_dvd_mul_left p hdvd
      have h2 : p ^ 2 ∣ Nat.card H := h1.trans (Subgroup.card_subgroup_dvd_card ρ.range)
      have := hH 2 h2
      omega
    have hcop : Nat.Coprime (Nat.card U') U'.index := by
      rw [hcardU']
      exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 hindex
    obtain ⟨K, hK⟩ := Subgroup.exists_left_complement'_of_coprime hcop
    let e : ρ.range ⧸ U' ≃* K := hK.QuotientMulEquiv
    let ψ : A →* H := ρ.range.subtype.comp (K.subtype.comp (e.toMonoidHom.comp
      ((QuotientGroup.mk' U').comp ρ')))
    refine ⟨ψ, le_antisymm (fun a ha => ?_) (fun a ha => ?_)⟩
    · have h1 : ψ a = 1 := ha
      have h2 : e (QuotientGroup.mk' U' (ρ' a)) = 1 := by
        apply K.subtype_injective
        apply ρ.range.subtype_injective
        simpa [ψ] using h1
      have h3 : QuotientGroup.mk' U' (ρ' a) = 1 := e.injective (by rw [h2, map_one])
      have h4 : ρ' a ∈ U' := (QuotientGroup.eq_one_iff _).1 h3
      obtain ⟨n, hn, hnρ⟩ := h4
      have h5 : n⁻¹ * a ∈ ρ.ker := by
        rw [MonoidHom.mem_ker]
        have h6 : ρ n = ρ a := congrArg Subtype.val (show ρ' n = ρ' a from hnρ)
        rw [map_mul, map_inv, h6, inv_mul_cancel]
      have : a = n * (n⁻¹ * a) := by group
      rw [this]
      exact (pCore p A).mul_mem hn (hkerN h5)
    · have : ρ' a ∈ U' := Subgroup.mem_map_of_mem ρ' ha
      have h3 : QuotientGroup.mk' U' (ρ' a) = 1 := (QuotientGroup.eq_one_iff _).2 this
      change ρ.range.subtype (K.subtype (e (QuotientGroup.mk' U' (ρ' a)))) = 1
      rw [h3, map_one]
      rfl

theorem exists_hom_ker_eq_pCore_aut (hp2 : p ≠ 2) (hP : IsPGroup p P)
    (hr : pRank p (⊤ : Subgroup P) ≤ 2) :
    ∃ φ : MulAut P →* GL (Fin 2) (ZMod p), φ.ker = pCore p (MulAut P) := by
  have hp1 := hp.out.one_lt
  rcases subsingleton_or_nontrivial P with hsub | hnt
  · have hsub' : Subsingleton (MulAut P) :=
      ⟨fun a b => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
    refine ⟨1, ?_⟩
    have : pCore p (MulAut P) = ⊤ := eq_top_iff.2 fun a _ => by
      rw [Subsingleton.elim a 1]
      exact Subgroup.one_mem _
    rw [this]
    ext a
    simp
  · obtain ⟨X, hXs, hfaith⟩ := exists_isSupercritical_faithful hp2 hP
    have := hXs.characteristic
    have hXp : IsPGroup p X := hP.to_subgroup X
    obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hXp
    obtain ⟨m, hm⟩ := (hXp.to_quotient (frattini X)).exists_card_eq
    have hXexp : ∀ x : X, x ^ p = 1 := fun x => Subtype.ext (by simpa using hXs.pow_eq_one x x.2)
    have hXr : pRank p (⊤ : Subgroup X) ≤ 2 := by
      rw [pRank_top_subtype]
      exact (pRank_mono hp1 le_top).trans hr
    have hcardW := (rank_two_exponent_prime_order_bound hXp hXexp hXr).2
    have hmle : m ≤ 2 := by
      rw [hm] at hcardW
      exact (Nat.pow_le_pow_iff_right hp1).1 hcardW
    obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hWcomm hWpow hm
    have hker : IsPGroup p (frattiniAction X).ker := by
      refine isPGroup_of_coprime_eq_one fun a ha => ?_
      have ha' : (orderOf (a : MulAut P)).Coprime p := by
        rwa [← Subgroup.orderOf_coe a] at ha
      exact Subtype.ext (hfaith a ha' ((mem_ker_frattiniAction_iff X a).1 a.2))
    have hH : ∀ k : ℕ, p ^ k ∣ Nat.card (MulAut (X ⧸ frattini X)) → k ≤ 1 := fun k hk =>
      pow_le_of_dvd_card_mulAut hWcomm hWpow hm hmle hk
    obtain ⟨ψ, hψ⟩ := exists_hom_ker_eq_pCore (frattiniAction X) hker hH
    obtain ⟨ι, hι⟩ := exists_injective_GL_le_two (R := ZMod p) hmle
    refine ⟨(ι.comp (elemAutEquivGL e).toMonoidHom).comp ψ, ?_⟩
    rw [← hψ]
    ext a
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    constructor
    · intro h
      exact (elemAutEquivGL e).injective (hι (by rw [h, map_one, map_one]))
    · intro h
      rw [h, map_one, map_one]

theorem prime_dvd_card_aut_of_three (hP : IsPGroup 3 P) (hr : pRank 3 (⊤ : Subgroup P) ≤ 2)
    {q : ℕ} (hq : q.Prime) (hdvd : q ∣ Nat.card (MulAut P)) : q = 2 ∨ q = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ, hφ⟩ := exists_hom_ker_eq_pCore_aut (p := 3) (by norm_num) hP hr
  have hcard : Nat.card (MulAut P) = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (r := 3) (G := MulAut P)).exists_card_eq
  have hGL : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
    rw [card_GL_zmod (p := 3) 2]
    simp [Fin.prod_univ_two]
  have hrange : Nat.card φ.range ∣ 48 := hGL ▸ Subgroup.card_subgroup_dvd_card φ.range
  rw [hcard, hφ, hk] at hdvd
  rcases (Nat.Prime.dvd_mul hq).1 hdvd with h | h
  · have h48 : q ∣ 2 ^ 4 * 3 := (h.trans hrange).trans (by norm_num)
    rcases (Nat.Prime.dvd_mul hq).1 h48 with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h2))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h3)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (hq.dvd_of_dvd_pow h))

end A125

section A123

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_monoidHom_le {p : ℕ} [hp : Fact p.Prime] {Q Z : Type*} [Group Q] [Finite Q]
    [Group Z] [Finite Z] (hcomm : ∀ a b : Q, a * b = b * a) (hpow : ∀ a : Q, a ^ p = 1)
    (hZ : Nat.card Z = p) : Nat.card (Q →* Z) ≤ Nat.card Q := by
  have hQp : IsPGroup p Q := fun a => ⟨1, by simpa using hpow a⟩
  obtain ⟨m, hm⟩ := hQp.exists_card_eq
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hcomm hpow hm
  have hcyc : IsCyclic Z := isCyclic_of_prime_card hZ
  subst hZ
  have : NeZero (Nat.card Z) := ⟨Nat.card_pos.ne'⟩
  let c : Multiplicative (ZMod (Nat.card Z)) ≃* Z := zmodCyclicMulEquiv hcyc
  let A : (Q →* Z) → ((Fin m → ZMod (Nat.card Z)) →+ ZMod (Nat.card Z)) := fun f =>
    { toFun := fun v => Multiplicative.toAdd (c.symm (f (e.symm (Multiplicative.ofAdd v))))
      map_zero' := by
        simp only [ofAdd_zero, map_one, toAdd_one]
      map_add' := fun v w => by
        simp only [ofAdd_add, map_mul, toAdd_mul] }
  let Ψ : (Q →* Z) → (Fin m → ZMod (Nat.card Z)) := fun f i => A f (Pi.single i 1)
  have hΨ : Function.Injective Ψ := by
    intro f f' h
    have hL : AddMonoidHom.toZModLinearMap (Nat.card Z) (A f) =
        AddMonoidHom.toZModLinearMap (Nat.card Z) (A f') := by
      apply LinearMap.pi_ext
      intro i x
      have hx : (Pi.single i x : Fin m → ZMod (Nat.card Z)) = x • (Pi.single i 1) := by
        ext j
        by_cases hij : j = i
        · subst hij
          simp
        · simp [hij]
      simp only [hx, map_smul]
      rw [show AddMonoidHom.toZModLinearMap (Nat.card Z) (A f) (Pi.single i 1) =
        AddMonoidHom.toZModLinearMap (Nat.card Z) (A f') (Pi.single i 1) from congrFun h i]
    ext q
    obtain ⟨v, rfl⟩ := e.symm.surjective q
    have h1 : Multiplicative.toAdd (c.symm (f (e.symm v))) =
        Multiplicative.toAdd (c.symm (f' (e.symm v))) :=
      congrArg (fun φ => φ (Multiplicative.toAdd v)) hL
    exact c.symm.injective (Multiplicative.toAdd.injective h1)
  have hfin : Finite (Fin m → ZMod (Nat.card Z)) := inferInstance
  calc Nat.card (Q →* Z) ≤ Nat.card (Fin m → ZMod (Nat.card Z)) :=
        Nat.card_le_card_of_injective Ψ hΨ
    _ = Nat.card Q := by
        rw [hm, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin,
          Nat.card_zmod]

omit [Group P] in
theorem commutatorElement_mul_center_left {G : Type*} [Group G] {a c : G} (y : G)
    (hc : c ∈ Subgroup.center G) : ⁅a * c, y⁆ = ⁅a, y⁆ := by
  have hcy : c * y * c⁻¹ = y := by
    rw [← Subgroup.mem_center_iff.1 hc y]
    group
  calc ⁅a * c, y⁆ = a * (c * y * c⁻¹) * a⁻¹ * y⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅a, y⁆ := by
        rw [hcy]
        simp only [commutatorElement_def]

omit [Group P] in
theorem commutatorElement_mul_center_right {G : Type*} [Group G] {b d : G} (x : G)
    (hd : d ∈ Subgroup.center G) : ⁅x, b * d⁆ = ⁅x, b⁆ := by
  rw [← commutatorElement_inv, commutatorElement_mul_center_left x hd, commutatorElement_inv]

theorem range_conj_eq_ker_autQuotient_frattini {p : ℕ} [hp : Fact p.Prime] [Finite P]
    [CFSG.IsExtraspecial p P] :
    (MulAut.conj : P →* MulAut P).range = (autQuotient (frattini P)).ker := by
  have hPp : IsPGroup p P := CFSG.IsExtraspecial.isPGroup p P
  set Z := Subgroup.center P with hZdef
  have hZcard : Nat.card Z = p := CFSG.IsExtraspecial.center_order_p p P
  have hQel : CFSG.IsElementaryAbelian p (P ⧸ Z) :=
    CFSG.IsExtraspecial.quotient_elementary_abelian p P
  have hQnt : Nontrivial (P ⧸ Z) := CFSG.IsExtraspecial.quotient_nontrivial p P
  have hQcomm : ∀ a b : P ⧸ Z, a * b = b * a := fun a b => mul_comm' a b
  have hQpow : ∀ a : P ⧸ Z, a ^ p = 1 := fun a =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (CFSG.IsElementaryAbelian.exponent_dvd_p p (P ⧸ Z)) a
  have hcommZ : ∀ a b : P, ⁅a, b⁆ ∈ Z := by
    intro a b
    rw [← QuotientGroup.eq_one_iff]
    have := map_commutatorElement (QuotientGroup.mk' Z) a b
    change ((⁅a, b⁆ : P) : P ⧸ Z) = 1
    rw [show ((⁅a, b⁆ : P) : P ⧸ Z) = ⁅(a : P ⧸ Z), (b : P ⧸ Z)⁆ from this]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hQcomm _ _)
  have hpowZ : ∀ x : P, x ^ p ∈ Z := fun x => by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hQpow x
  have hΦZ : frattini P ≤ Z := frattini_le_of_commutator_pow_mem (p := p) Z hcommZ hpowZ
  have hnc : ∃ a b : P, a * b ≠ b * a := by
    by_contra h
    push Not at h
    obtain ⟨q, hq⟩ := exists_ne (1 : P ⧸ Z)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact hq ((QuotientGroup.eq_one_iff x).2 (Subgroup.mem_center_iff.2 fun g => h g x))
  have hcommle : commutator P ≤ Z := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    exact fun a _ b _ => hcommZ a b
  have hcommP : commutator P = Z := by
    obtain ⟨a, b, hab⟩ := hnc
    have hne : commutator P ≠ ⊥ := by
      intro h
      have hmem : ⁅a, b⁆ ∈ commutator P := by
        rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hab hmem
    have hdvd : Nat.card (commutator P) ∣ p := hZcard ▸ Subgroup.card_dvd_of_le hcommle
    rcases (Nat.dvd_prime hp.out).1 hdvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.1 h1) hne
    · exact Subgroup.eq_of_le_of_card_ge hcommle (by rw [h1, hZcard])
  have hrange : (MulAut.conj : P →* MulAut P).range ≤ (autQuotient (frattini P)).ker := by
    rintro _ ⟨g, rfl⟩
    rw [mem_ker_autQuotient]
    intro x
    have := commutator_mem_frattini hPp x⁻¹ g
    simpa [commutatorElement_def, mul_assoc] using this
  set C := (autQuotient (frattini P)).ker with hC
  have hfα : ∀ α ∈ C, ∀ x : P, x⁻¹ * α x ∈ Z := fun α hα x =>
    hΦZ ((mem_ker_autQuotient _).1 hα x)
  have hfix : ∀ α ∈ C, ∀ z ∈ Z, α z = z := by
    intro α hα z hz
    rw [← hcommP] at hz
    have hle : commutator P ≤ MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id P) := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      change α ⁅a, b⁆ = ⁅a, b⁆
      obtain ⟨ca, hcaZ, hca⟩ : ∃ c ∈ Z, α a = a * c := ⟨a⁻¹ * α a, hfα α hα a, by group⟩
      obtain ⟨cb, hcbZ, hcb⟩ : ∃ c ∈ Z, α b = b * c := ⟨b⁻¹ * α b, hfα α hα b, by group⟩
      rw [show α ⁅a, b⁆ = ⁅α a, α b⁆ from map_commutatorElement α.toMonoidHom a b, hca, hcb,
        commutatorElement_mul_center_left _ hcaZ, commutatorElement_mul_center_right _ hcbZ]
    exact hle hz
  let φ : (α : MulAut P) → α ∈ C → (P →* Z) := fun α hα =>
    { toFun := fun x => ⟨x⁻¹ * α x, hfα α hα x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        change (x * y)⁻¹ * α (x * y) = (x⁻¹ * α x) * (y⁻¹ * α y)
        have hc := Subgroup.mem_center_iff.1 (hfα α hα x) y⁻¹
        calc (x * y)⁻¹ * α (x * y) = y⁻¹ * (x⁻¹ * α x) * α y := by rw [map_mul]; group
          _ = (x⁻¹ * α x) * y⁻¹ * α y := by rw [hc]
          _ = (x⁻¹ * α x) * (y⁻¹ * α y) := by group }
  have hφker : ∀ (α : MulAut P) (hα : α ∈ C), Z ≤ (φ α hα).ker := fun α hα z hz => by
    apply Subtype.ext
    change z⁻¹ * α z = 1
    rw [hfix α hα z hz, inv_mul_cancel]
  let Θ : C → (P ⧸ Z →* Z) := fun α => QuotientGroup.lift Z (φ α.1 α.2) (hφker α.1 α.2)
  have hΘ : Function.Injective Θ := by
    intro α β h
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    have h1 := congrArg (fun F : P ⧸ Z →* Z => ((F (x : P ⧸ Z) : Z) : P)) h
    simp only [Θ, QuotientGroup.lift_mk] at h1
    change x⁻¹ * α.1 x = x⁻¹ * β.1 x at h1
    exact mul_left_cancel h1
  have : Finite (P ⧸ Z →* Z) :=
    Finite.of_injective (fun f : P ⧸ Z →* Z => (f : P ⧸ Z → Z)) DFunLike.coe_injective
  have h1 : Nat.card C ≤ Nat.card (P ⧸ Z →* Z) := Nat.card_le_card_of_injective Θ hΘ
  have h2 : Nat.card (P ⧸ Z →* Z) ≤ Nat.card (P ⧸ Z) :=
    card_monoidHom_le hQcomm hQpow hZcard
  have hker : (MulAut.conj : P →* MulAut P).ker = Z := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h x
      have := congrArg (fun φ : MulAut P => φ x) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    · intro h
      ext x
      simp only [MulAut.conj_apply, MulAut.one_apply]
      rw [mul_inv_eq_iff_eq_mul]
      exact (h x).symm
  have h3 : Nat.card (MulAut.conj : P →* MulAut P).range = Nat.card (P ⧸ Z) := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange
      (MulAut.conj : P →* MulAut P)).toEquiv]
    exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv
  exact Subgroup.eq_of_le_of_card_ge hrange (h1.trans (h2.trans h3.ge))

end A123

end CFSG.Quasithin
