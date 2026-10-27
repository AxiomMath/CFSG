module

public import CFSG.Quasithin.Background.E1Param
public import CFSG.Quasithin.SteinbergBMAlternatingFiveProperSolvable
public import CFSG.GroupTheory.ABGLocalTools.Constraint

public section

namespace CFSG.Quasithin.E1.LiftS5

open CFSG.Open Equiv CFSG.Quasithin

@[expose] def v0a : Perm (Fin 5) := swap 0 1 * swap 2 3

@[expose] def v0b : Perm (Fin 5) := swap 0 2 * swap 1 3

@[expose] def v0c : Perm (Fin 5) := swap 0 3 * swap 1 2

@[expose] def v0list : List (Perm (Fin 5)) := [1, v0a, v0b, v0c]

@[expose] def V0 : Subgroup (Perm (Fin 5)) where
  carrier := {x | x ∈ v0list}
  one_mem' := by decide +kernel
  mul_mem' := by
    have key : ∀ x ∈ v0list, ∀ y ∈ v0list, x * y ∈ v0list := by decide +kernel
    exact fun {a b} ha hb => key a ha b hb
  inv_mem' := by
    have key : ∀ x ∈ v0list, x⁻¹ ∈ v0list := by decide +kernel
    exact fun {a} ha => key a ha

theorem mem_V0 {x : Perm (Fin 5)} : x ∈ V0 ↔ x ∈ v0list := Iff.rfl

theorem card_V0 : Nat.card ↥V0 = 4 := by
  have : (V0 : Set (Perm (Fin 5))) = ↑(v0list.toFinset) := by
    ext x; simp [mem_V0]
  rw [← SetLike.coe_sort_coe, this, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  decide +kernel

theorem V0_le_alternatingGroup : V0 ≤ alternatingGroup (Fin 5) := by
  have key : ∀ x ∈ v0list, Perm.sign x = 1 := by decide +kernel
  intro x hx
  exact Perm.mem_alternatingGroup.mpr (key x hx)

theorem orders_of_not_normalizes : ∀ g : Perm (Fin 5), ¬ (∀ v ∈ v0list, g * v * g⁻¹ ∈ v0list) →
    (∃ v ∈ v0list, ∃ w ∈ v0list, (v * (g * w * g⁻¹)) ^ 3 = 1 ∧ v * (g * w * g⁻¹) ≠ 1) ∧
      (∃ v ∈ v0list, ∃ w ∈ v0list, (v * (g * w * g⁻¹)) ^ 5 = 1 ∧ v * (g * w * g⁻¹) ≠ 1) := by
  decide +kernel

theorem eq_one_of_comm : ∀ g : Perm (Fin 5),
    (g * (swap 0 1 * swap 1 2) = (swap 0 1 * swap 1 2) * g ∧
      g * (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4) =
        (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4) * g) → g = 1 := by
  decide +kernel

theorem mem_normalizer_of_conj_le {X : Type*} [Group X] [Finite X] {W : Subgroup X} {g : X}
    (h : ∀ w ∈ W, g * w * g⁻¹ ∈ W) : g ∈ Subgroup.normalizer (W : Set X) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : W.map (MulAut.conj g).toMonoidHom ≤ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem exists_conj_eq_V0 {V : Subgroup (Perm (Fin 5))} (hVA : V ≤ alternatingGroup (Fin 5))
    (hV4 : Nat.card ↥V = 4) :
    ∃ g : Perm (Fin 5), V.map (MulAut.conj g).toMonoidHom = V0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A5 := alternatingGroup (Fin 5) with hA5def
  have hA60 : Nat.card ↥A5 = 60 := by
    rw [hA5def, nat_card_alternatingGroup, Nat.card_fin]; rfl
  have hsyl : ∀ W : Subgroup (Perm (Fin 5)), W ≤ A5 → Nat.card ↥W = 4 →
      ∃ P : Sylow 2 ↥A5, (P : Subgroup ↥A5) = W.subgroupOf A5 := by
    intro W hWA hW4
    have hc : Nat.card ↥(W.subgroupOf A5) = 4 := by
      rw [← hW4]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWA).toEquiv
    have h2 : IsPGroup 2 ↥(W.subgroupOf A5) := IsPGroup.of_card (n := 2) (by rw [hc]; norm_num)
    have hidx : ¬ 2 ∣ (W.subgroupOf A5).index := by
      have := Subgroup.card_mul_index (W.subgroupOf A5)
      rw [hc, hA60] at this
      have h15 : (W.subgroupOf A5).index = 15 := by omega
      rw [h15]; decide
    exact ⟨h2.toSylow hidx, rfl⟩
  obtain ⟨P, hP⟩ := hsyl V hVA hV4
  obtain ⟨P0, hP0⟩ := hsyl V0 V0_le_alternatingGroup card_V0
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥A5 P P0
  refine ⟨(g : Perm (Fin 5)), ?_⟩
  have h1 : ((g • P : Sylow 2 ↥A5) : Subgroup ↥A5) = (P : Subgroup ↥A5).map
      (MulAut.conj g).toMonoidHom := Sylow.coe_subgroup_smul
  rw [hg, hP0, hP] at h1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyA : y ∈ A5 := hVA hy
    have : (MulAut.conj g).toMonoidHom ⟨y, hyA⟩ ∈ V0.subgroupOf A5 := by
      rw [h1]; exact ⟨⟨y, hyA⟩, hy, rfl⟩
    exact this
  · intro hx
    have hxA : x ∈ A5 := V0_le_alternatingGroup hx
    have : (⟨x, hxA⟩ : ↥A5) ∈ (V.subgroupOf A5).map (MulAut.conj g).toMonoidHom := by
      rw [← h1]; exact hx
    obtain ⟨y, hy, hyx⟩ := this
    refine ⟨(y : Perm (Fin 5)), hy, ?_⟩
    have := congrArg Subtype.val hyx
    simpa [MulAut.conj_apply] using this

theorem le_normalizer_or_alt_le {V K : Subgroup (Perm (Fin 5))}
    (hVA : V ≤ alternatingGroup (Fin 5)) (hV4 : Nat.card ↥V = 4) (hVK : V ≤ K) :
    K ≤ Subgroup.normalizer (V : Set (Perm (Fin 5))) ∨ alternatingGroup (Fin 5) ≤ K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_conj_eq_V0 hVA hV4
  have hmemV : ∀ x, x ∈ V ↔ g * x * g⁻¹ ∈ V0 := by
    intro x
    rw [← hg]
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have hyx' : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      have : y = x := by simpa using hyx'
      rwa [← this]
  by_cases hK : K ≤ Subgroup.normalizer (V : Set (Perm (Fin 5)))
  · exact Or.inl hK
  right
  obtain ⟨k, hkK, hkN⟩ := Set.not_subset.mp hK
  set k' := g * k * g⁻¹ with hk'
  have hnot : ¬ (∀ v ∈ v0list, k' * v * k'⁻¹ ∈ v0list) := by
    intro h
    apply hkN
    refine mem_normalizer_of_conj_le fun w hw => ?_
    rw [hmemV] at hw ⊢
    have := h _ hw
    have e : g * (k * w * k⁻¹) * g⁻¹ = k' * (g * w * g⁻¹) * k'⁻¹ := by rw [hk']; group
    rw [e]
    exact this
  obtain ⟨⟨v, hv, w, hw, h3, h31⟩, ⟨v', hv', w', hw', h5, h51⟩⟩ := orders_of_not_normalizes k' hnot
  have hconjV : ∀ v ∈ v0list, g⁻¹ * v * g ∈ V := fun v hv =>
    (hmemV _).2 (by
      have e : g * (g⁻¹ * v * g) * g⁻¹ = v := by group
      rw [e]; exact hv)
  set J := K ⊓ alternatingGroup (Fin 5) with hJ
  have hVJ : V ≤ J := le_inf hVK hVA
  have hmem : ∀ v ∈ v0list, ∀ w ∈ v0list, g⁻¹ * (v * (k' * w * k'⁻¹)) * g ∈ J := by
    intro v hv w hw
    have e : g⁻¹ * (v * (k' * w * k'⁻¹)) * g = (g⁻¹ * v * g) * (k * (g⁻¹ * w * g) * k⁻¹) := by
      rw [hk']; group
    rw [e]
    have hv1 := hVJ (hconjV v hv)
    have hw1 := hVJ (hconjV w hw)
    exact J.mul_mem hv1 ⟨K.mul_mem (K.mul_mem hkK hw1.1) (K.inv_mem hkK),
      (alternatingGroup.normal (α := Fin 5)).conj_mem _ hw1.2 k⟩
  have hord : ∀ x : Perm (Fin 5), ∀ n : ℕ, n.Prime → x ^ n = 1 → x ≠ 1 →
      orderOf (g⁻¹ * x * g) = n := by
    intro x n hn hx hx1
    have : Fact n.Prime := ⟨hn⟩
    refine orderOf_eq_prime ?_ ?_
    · have e : (g⁻¹ * x * g) ^ n = g⁻¹ * x ^ n * g := by
        have := conj_pow (a := g⁻¹) (b := x) (i := n)
        simpa using this
      rw [e, hx]; group
    · intro h
      apply hx1
      have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      rw [this, h]; group
  have h3' : 3 ∣ Nat.card ↥J := by
    have := Subgroup.orderOf_dvd_natCard J (hmem v hv w hw)
    rwa [hord _ 3 Nat.prime_three h3 h31] at this
  have h5' : 5 ∣ Nat.card ↥J := by
    have := Subgroup.orderOf_dvd_natCard J (hmem v' hv' w' hw')
    rwa [hord _ 5 (by norm_num) h5 h51] at this
  have h4' : 4 ∣ Nat.card ↥J := hV4 ▸ Subgroup.card_dvd_of_le hVJ
  have h60 : 60 ∣ Nat.card ↥J := by
    have h12 : 12 ∣ Nat.card ↥J := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3' h4'
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 12 5) h12 h5'
  have hA60 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]; rfl
  have heq : J = alternatingGroup (Fin 5) := by
    refine Subgroup.eq_of_le_of_card_ge inf_le_right ?_
    rw [hA60]
    exact Nat.le_of_dvd Nat.card_pos h60
  rw [← heq]
  exact inf_le_left

theorem not_isSolvable_alt : ¬ Group.IsSolvable ↥(alternatingGroup (Fin 5)) := by
  intro h
  apply Equiv.Perm.not_isSolvable_fin_5
  exact Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 5)).subtype Perm.sign
    (fun x hx => ⟨⟨x, hx⟩, rfl⟩)

theorem le_normalizer_of_isSolvable {V K : Subgroup (Perm (Fin 5))}
    (hVA : V ≤ alternatingGroup (Fin 5)) (hV4 : Nat.card ↥V = 4) (hVK : V ≤ K)
    (hK : Group.IsSolvable ↥K) : K ≤ Subgroup.normalizer (V : Set (Perm (Fin 5))) :=
  (le_normalizer_or_alt_le hVA hV4 hVK).resolve_right fun h =>
    not_isSolvable_alt (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h))

theorem alt_le_of_not_isSolvable {K : Subgroup (Perm (Fin 5))} (hK : ¬ Group.IsSolvable ↥K) :
    alternatingGroup (Fin 5) ≤ K := by
  by_contra h
  apply hK
  set A5 := alternatingGroup (Fin 5) with hA5
  have hprop : (K ⊓ A5).subgroupOf A5 < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => h ?_
    intro x hx
    have : (⟨x, hx⟩ : ↥A5) ∈ (K ⊓ A5).subgroupOf A5 := by rw [htop]; trivial
    exact this.1
  have hs : Group.IsSolvable ↥((K ⊓ A5).subgroupOf A5) :=
    SteinbergBM.alternating_five_proper_subgroup_solvable (by simp) hprop
  have hs' : Group.IsSolvable ↥(A5.subgroupOf K) := by
    let e : ↥(A5.subgroupOf K) →* ↥((K ⊓ A5).subgroupOf A5) :=
      { toFun := fun x => ⟨⟨(x : ↥K), x.2⟩, ⟨(x : ↥K).2, x.2⟩⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Group.isSolvable_of_isSolvable_injective (f := e) ?_
    intro x y hxy
    have := congrArg (fun z : ↥((K ⊓ A5).subgroupOf A5) => ((z : ↥A5) : Perm (Fin 5))) hxy
    exact Subtype.ext (Subtype.ext this)
  exact Group.isSolvable_of_ker_le_range (A5.subgroupOf K).subtype
    (Perm.sign.comp K.subtype) (fun x hx => ⟨⟨x, by
      rw [Subgroup.mem_subgroupOf]
      exact Perm.mem_alternatingGroup.mpr hx⟩, rfl⟩)

theorem not_alt_le_normalizer {V : Subgroup (Perm (Fin 5))} (hVA : V ≤ alternatingGroup (Fin 5))
    (hV4 : Nat.card ↥V = 4) :
    ¬ alternatingGroup (Fin 5) ≤ Subgroup.normalizer (V : Set (Perm (Fin 5))) := by
  intro h
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hn : (V.subgroupOf (alternatingGroup (Fin 5))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVA).mpr h
  have hc : Nat.card ↥(V.subgroupOf (alternatingGroup (Fin 5))) = 4 := by
    rw [← hV4]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVA).toEquiv
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (V.subgroupOf (alternatingGroup (Fin 5))) with
    h1 | h1
  · rw [h1, Subgroup.card_bot] at hc; norm_num at hc
  · rw [h1, Subgroup.card_top, nat_card_alternatingGroup, Nat.card_fin] at hc
    exact absurd hc (by decide)

theorem eq_bot_of_isSolvable {N : Subgroup (Perm (Fin 5))}
    (hN : alternatingGroup (Fin 5) ≤ Subgroup.normalizer (N : Set (Perm (Fin 5))))
    (hs : Group.IsSolvable ↥N) : N = ⊥ := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  set A5 := alternatingGroup (Fin 5) with hA5
  have hn : (N.subgroupOf A5).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hN g.2) n).mp hn⟩
  have hbot : N ⊓ A5 = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf A5) with h1 | h1
    · refine eq_bot_iff.mpr fun x hx => ?_
      have : (⟨x, hx.2⟩ : ↥A5) ∈ N.subgroupOf A5 := hx.1
      rw [h1, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · exfalso
      apply not_isSolvable_alt
      have hle : A5 ≤ N := fun x hx => by
        have : (⟨x, hx⟩ : ↥A5) ∈ N.subgroupOf A5 := by rw [h1]; trivial
        exact this
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have hcomm : ∀ n ∈ N, ∀ σ ∈ A5, n * σ = σ * n := by
    intro n hnN σ hσ
    have h1 : n * σ * n⁻¹ * σ⁻¹ ∈ N := by
      have e : n * σ * n⁻¹ * σ⁻¹ = n * (σ * n⁻¹ * σ⁻¹) := by group
      rw [e]
      exact N.mul_mem hnN ((Subgroup.mem_normalizer_iff.mp (hN hσ) n⁻¹).mp (N.inv_mem hnN))
    have h2 : n * σ * n⁻¹ * σ⁻¹ ∈ A5 :=
      A5.mul_mem ((alternatingGroup.normal (α := Fin 5)).conj_mem σ hσ n) (A5.inv_mem hσ)
    have h3 : n * σ * n⁻¹ * σ⁻¹ ∈ N ⊓ A5 := ⟨h1, h2⟩
    rw [hbot, Subgroup.mem_bot] at h3
    calc n * σ = (n * σ * n⁻¹ * σ⁻¹) * (σ * n) := by group
      _ = σ * n := by rw [h3, one_mul]
  have hc3 : Perm.sign (swap 0 1 * swap 1 2 : Perm (Fin 5)) = 1 ∧
      Perm.sign (swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4 : Perm (Fin 5)) = 1 := by decide
  refine eq_bot_iff.mpr fun n hn => Subgroup.mem_bot.mpr (eq_one_of_comm n ⟨?_, ?_⟩)
  · exact hcomm n hn _ (Perm.mem_alternatingGroup.mpr hc3.1)
  · exact hcomm n hn _ (Perm.mem_alternatingGroup.mpr hc3.2)

section NParam

variable {G : Type} [Group G] [Finite G]

open E1 A1b

omit [Finite G] in
theorem isElemAbelian_conjSub' {A : Subgroup G} (hA : IsElemAbelian 2 A) (g : G) :
    IsElemAbelian 2 (conjSub g A) := by
  obtain ⟨hc, h2⟩ := hA
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    have := congrArg Subtype.val (hc.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
    simp only [Subgroup.coe_mul] at this
    show (a : G) * b = b * a
    rw [← ha, ← hb]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * a' * g⁻¹ * (g * b' * g⁻¹) = g * (a' * b') * g⁻¹ := by group
      _ = g * (b' * a') * g⁻¹ := by rw [this]
      _ = g * b' * g⁻¹ * (g * a' * g⁻¹) := by group
  · obtain ⟨x', hx', rfl⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_pow, h2 x' hx']; group

theorem one_lt_nParam_of_lift {H T A : Subgroup G} (ψ : ↥H →* Perm (Fin 5))
    (hA5 : alternatingGroup (Fin 5) ≤ ψ.range) (hT : IsSylowIn 2 T H) (hAT : A ≤ T)
    (hA : IsElemAbelian 2 A) (hψA : (A.subgroupOf H).map ψ ≤ alternatingGroup (Fin 5))
    (hψA4 : Nat.card ↥((A.subgroupOf H).map ψ) = 4) : 1 < nParam H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hT.le
  have hAH : A ≤ H := hAT.trans hTH
  set V := (A.subgroupOf H).map ψ with hVdef
  set A5 := alternatingGroup (Fin 5) with hA5def
  have hA60 : Nat.card ↥A5 = 60 := by
    rw [hA5def, nat_card_alternatingGroup, Nat.card_fin]; rfl
  have hψT2 : IsPGroup 2 ↥((T.subgroupOf H).map ψ) :=
    (hT.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm).map ψ
  have himg : ∀ h ∈ H, conjSub h A ≤ T → ((conjSub h A).subgroupOf H).map ψ = V := by
    intro h hh hAT'
    set P := (T.subgroupOf H).map ψ ⊓ A5 with hP
    have hP2 : IsPGroup 2 ↥P := hψT2.to_le inf_le_left
    have hP4 : Nat.card ↥P ≤ 4 := by
      obtain ⟨k, hk⟩ := hP2.exists_card_eq
      have hdvd : Nat.card ↥P ∣ 60 := hA60 ▸ Subgroup.card_dvd_of_le inf_le_right
      rw [hk] at hdvd ⊢
      have : k ≤ 2 := by
        by_contra hk2
        push Not at hk2
        have h8 : 2 ^ 3 ∣ 60 := (Nat.pow_dvd_pow 2 hk2).trans hdvd
        exact absurd h8 (by decide)
      calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
        _ = 4 := by norm_num
    have hVP : V ≤ P := le_inf (Subgroup.map_mono (Subgroup.subgroupOf_mono _ hAT)) hψA
    have hVeq : V = P := Subgroup.eq_of_le_of_card_ge hVP (by rw [hψA4]; exact hP4)
    set g : Perm (Fin 5) := ψ ⟨h, hh⟩ with hg
    have hconj : ((conjSub h A).subgroupOf H).map ψ = V.map (MulAut.conj g).toMonoidHom := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy' : h⁻¹ * (y : G) * h ∈ A := (mem_conjSub_iff).1 hy
        refine ⟨ψ (⟨h, hh⟩⁻¹ * y * ⟨h, hh⟩), ⟨⟨h, hh⟩⁻¹ * y * ⟨h, hh⟩, ?_, rfl⟩, ?_⟩
        · show ((⟨h, hh⟩⁻¹ * y * ⟨h, hh⟩ : ↥H) : G) ∈ A
          simpa using hy'
        · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, hg]
          group
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        have hz' : (z : G) ∈ A := hz
        refine ⟨⟨h, hh⟩ * z * (⟨h, hh⟩)⁻¹, ?_, ?_⟩
        · show ((⟨h, hh⟩ * z * (⟨h, hh⟩)⁻¹ : ↥H) : G) ∈ conjSub h A
          rw [mem_conjSub_iff]
          simpa [mul_assoc] using hz'
        · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, hg]
    have hcard : Nat.card ↥(((conjSub h A).subgroupOf H).map ψ) = 4 := by
      rw [hconj, Subgroup.card_map_of_injective (MulAut.conj g).injective, hψA4]
    have hle : ((conjSub h A).subgroupOf H).map ψ ≤ P := by
      refine le_inf (Subgroup.map_mono (Subgroup.subgroupOf_mono _ hAT')) ?_
      rw [hconj]
      rintro _ ⟨y, hy, rfl⟩
      exact (alternatingGroup.normal (α := Fin 5)).conj_mem y (hψA hy) g
    rw [hVeq]
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, ← hVeq, hψA4])
  set Y : Subgroup G := ((Subgroup.normalizer (V : Set (Perm (Fin 5)))).comap ψ).map H.subtype
    with hYdef
  have hmemY : ∀ (x : G) (hx : x ∈ H), ψ ⟨x, hx⟩ ∈ Subgroup.normalizer (V : Set (Perm (Fin 5))) →
      x ∈ Y := fun x hx h => ⟨⟨x, hx⟩, h, rfl⟩
  set Ω : Set (Subgroup G) := {B | ∃ h ∈ H, B = conjSub h A} with hΩdef
  have hΩ : IsInvColl H Ω := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨h, hh, rfl⟩ x hx
      rw [mem_conjSub_iff] at hx
      have : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
      rw [this]
      exact H.mul_mem (H.mul_mem hh (hAH hx)) (H.inv_mem hh)
    · rintro _ ⟨h, hh, rfl⟩
      exact isElemAbelian_conjSub' hA h
    · rintro _ ⟨h, hh, rfl⟩ g hg
      exact ⟨g * h, H.mul_mem hg hh, by rw [conjSub_mul]⟩
  have hE : ∀ A' ∈ Ω, A' ≤ T → ∀ K, IsE 1 H T A' K → K ≤ Y := by
    rintro _ ⟨h, hh, rfl⟩ hA'T K ⟨hKH, hτ, -, hrank⟩
    set A' := conjSub h A with hA'def
    have hA'e := isElemAbelian_conjSub' hA h
    have hA'K : A' ≤ K := by
      intro a ha
      refine (hτ ⟨hA'T ha, ?_, fun b hb => ?_⟩).2
      · exact LieType.BorelTits.le_normalizer_pCoreOf 2 H (hΩ.le _ ⟨h, hh, rfl⟩ ha)
      · have hc := hA'e.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
        have hab : a * b = b * a := congrArg Subtype.val hc
        rw [commutatorElement_def, hab]
        simp
    set f : ↥K →* Perm (Fin 5) := ψ.comp (Subgroup.inclusion hKH) with hf
    have hfA : (A'.subgroupOf K).map f = V := by
      rw [← himg h hh hA'T]
      ext x
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, hf, MonoidHom.comp_apply]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨Subgroup.inclusion hKH y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨(y : G), hA'K hy⟩, hy, rfl⟩
    have hVK : V ≤ f.range := by
      rw [← hfA]; exact Subgroup.map_le_range _ _
    rcases le_normalizer_or_alt_le hψA hψA4 hVK with hN | hAK
    · intro x hx
      exact hmemY x (hKH hx) (hN ⟨⟨x, hx⟩, rfl⟩)
    · exfalso
      have hkill : ∀ M : Subgroup ↥K, M.Normal → Group.IsSolvable ↥M → M ≤ f.ker := by
        intro M hM hMs
        have hbot : M.map f = ⊥ := by
          refine eq_bot_of_isSolvable ?_ ?_
          · intro σ hσ
            obtain ⟨k, rfl⟩ := hAK hσ
            rw [Subgroup.mem_normalizer_iff]
            intro y
            constructor
            · rintro ⟨m, hm, rfl⟩
              exact ⟨k * m * k⁻¹, hM.conj_mem m hm k, by simp⟩
            · rintro ⟨m, hm, hmy⟩
              refine ⟨k⁻¹ * m * k, by simpa using hM.conj_mem m hm k⁻¹, ?_⟩
              have : y = f k⁻¹ * (f k * y * (f k)⁻¹) * f k := by simp [mul_assoc]
              rw [this, ← hmy]; simp [mul_assoc]
          · have h1 : Group.IsSolvable ↥((f.comp M.subtype).range) :=
              Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective (f.comp M.subtype))
            rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h1
        intro m hm
        have : f m ∈ M.map f := ⟨m, hm, rfl⟩
        rw [hbot, Subgroup.mem_bot] at this
        exact this
      have hbar : ∀ (M : Subgroup ↥K) [M.Normal], M ≤ f.ker →
          4 ≤ Nat.card ↥((A'.subgroupOf K).map (QuotientGroup.mk' M)) := by
        intro M _ hMk
        set f' := QuotientGroup.lift M f hMk with hf'
        have hcomp : f'.comp (QuotientGroup.mk' M) = f := by
          ext x; simp [hf']
        have h1 : ((A'.subgroupOf K).map (QuotientGroup.mk' M)).map f' =
            (A'.subgroupOf K).map f := by
          rw [Subgroup.map_map, hcomp]
        have h2 := Subgroup.card_map_dvd (H := (A'.subgroupOf K).map (QuotientGroup.mk' M)) f'
        rw [h1, hfA, hψA4] at h2
        exact Nat.le_of_dvd Nat.card_pos h2
      rcases hrank with ⟨-, h2⟩ | ⟨-, h2⟩
      · have hnil : Group.IsNilpotent ↥(CFSG.Open.pCore 2 ↥K) :=
          (CFSG.LieType.BorelTits.pCore_isPGroup 2).isNilpotent
        have hO : CFSG.Open.pCore 2 ↥K ≤ f.ker := hkill _
          (CFSG.LieType.BorelTits.pCore_normal 2) inferInstance
        have := @hbar _ (CFSG.LieType.BorelTits.pCore_normal 2) hO
        unfold barO2 at h2
        omega
      · have hO : CFSG.solvableRadical ↥K ≤ f.ker := hkill _
          (ABGLocalTools.solvableRadical_normal) ABGLocalTools.solvableRadical_isSolvable
        have := @hbar _ ABGLocalTools.solvableRadical_normal hO
        unfold barRad at h2
        omega
  have hWN : H ⊓ Subgroup.normalizer (weakClosure T Ω : Set G) ≤ Y := by
    set W := weakClosure T Ω with hWdef
    have hWT : W ≤ T := iSup₂_le fun B _ => iSup_le fun hB => hB
    have hAW : A ≤ W := by
      have hA1 : A ∈ Ω := ⟨1, H.one_mem, by rw [conjSub_one]⟩
      exact le_iSup₂_of_le A hA1 (le_iSup_of_le hAT le_rfl)
    have hψW : (W.subgroupOf H).map ψ = V := by
      apply le_antisymm
      · have hW : W ≤ ((V.comap ψ).map H.subtype) := by
          refine iSup₂_le fun B hB => iSup_le fun hBT => ?_
          obtain ⟨h, hh, rfl⟩ := hB
          intro x hx
          have hxH : x ∈ H := hΩ.le _ ⟨h, hh, rfl⟩ hx
          refine ⟨⟨x, hxH⟩, ?_, rfl⟩
          show ψ ⟨x, hxH⟩ ∈ V
          rw [← himg h hh hBT]
          exact ⟨⟨x, hxH⟩, hx, rfl⟩
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨z, hz, hzy⟩ := hW hy
        have : z = y := Subtype.ext hzy
        rw [← this]; exact hz
      · exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ hAW)
    rintro x ⟨hxH, hxN⟩
    refine hmemY x hxH (mem_normalizer_of_conj_le fun v hv => ?_)
    rw [← hψW] at hv ⊢
    obtain ⟨y, hy, rfl⟩ := hv
    refine ⟨⟨x, hxH⟩ * y * (⟨x, hxH⟩)⁻¹, ?_, by simp⟩
    show _ ∈ W.subgroupOf H
    rw [Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp hxN y).mp hy
  rw [← not_le]
  intro hle
  have hInE : InE 1 H := (nParam_le_iff (n := 1) one_pos).1 (by exact_mod_cast hle)
  have hgen := hInE T hT Ω hΩ
  have hHY : H ≤ Y := by
    rw [← hgen]
    refine sup_le ?_ hWN
    exact iSup₂_le fun A' hA' => iSup_le fun hA'T => iSup₂_le fun K hK => hE A' hA' hA'T K hK
  apply not_alt_le_normalizer hψA hψA4
  intro σ hσ
  obtain ⟨⟨x, hx⟩, rfl⟩ := hA5 hσ
  obtain ⟨y, hy, hyx⟩ := hHY hx
  have : y = ⟨x, hx⟩ := Subtype.ext hyx
  rw [← this]
  exact hy

end NParam

end CFSG.Quasithin.E1.LiftS5
