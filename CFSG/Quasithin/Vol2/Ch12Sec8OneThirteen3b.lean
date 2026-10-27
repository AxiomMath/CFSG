module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneThirteen3a
public import CFSG.Quasithin.Vol2.Ch12Sec8OneThirteenZ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement Pointwise

namespace L128P

variable {G : Type} [Group G] [Finite G]

theorem exists_three_elt_lOne {T L V : Subgroup G} {n : ℕ} (h : Hyp1281One G T L V n)
    {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) {u u' : G} (hu : u ∈ V) (hu' : u' ∈ V)
    (huV₁ : u ∉ V₁) (hu'V₁ : u' ∉ V₁) (huu : u * u'⁻¹ ∉ V₁) :
    ∃ y ∈ lOne L V₁, (∃ k : ℕ, y ^ 3 ^ k = 1) ∧ y * u * y⁻¹ * u⁻¹ ∉ V₁ := by
  classical
  obtain ⟨-, hsq, hab⟩ := h.card_sq
  obtain ⟨hcV, -⟩ := h.natural
  let _ := zmodModuleOf hsq
  set a : Additive ↥V := Additive.ofMul ⟨u, hu⟩ with hadef
  set b : Additive ↥V := Additive.ofMul ⟨u', hu'⟩ with hbdef
  have hmem : ∀ x : Additive ↥V, x ∈ subOf (V := V) V₁ ↔
      ((Additive.toMul x : ↥V) : G) ∈ V₁ := fun x => mem_subOf
  have hab' : ∀ {x y : G} (hx : x ∈ V) (hy : y ∈ V) (hxV₁ : x ∉ V₁) (hxy : x * y⁻¹ ∉ V₁),
      Additive.ofMul (⟨x, hx⟩ : ↥V) ∉ subOf (V := V) V₁ ⊔ (ZMod 2) ∙
        Additive.ofMul (⟨y, hy⟩ : ↥V) := by
    intro x y hx hy hxV₁ hxy hmem'
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hmem'
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hq
    rcases zmod_two_cases t with rfl | rfl
    · rw [zero_smul, add_zero] at hpq
      exact hxV₁ (by have := (hmem p).1 hp; rwa [hpq] at this)
    · rw [one_smul] at hpq
      apply hxy
      have h1 := (hmem p).1 hp
      have h2 : p = Additive.ofMul (⟨x, hx⟩ : ↥V) - Additive.ofMul ⟨y, hy⟩ := by
        rw [← hpq]; abel
      rw [h2, toMul_sub, toMul_ofMul, toMul_ofMul, Subgroup.coe_div, div_eq_mul_inv] at h1
      exact h1
  have huu' : u' * u⁻¹ ∉ V₁ := fun h1 => huu (by
    have := V₁.inv_mem h1
    rwa [show (u' * u⁻¹)⁻¹ = u * u'⁻¹ by group] at this)
  obtain ⟨ρ, hρ3, hρa, hρb, hρP⟩ :=
    exists_rotation (hab' hu hu' huV₁ huu) (hab' hu' hu hu'V₁ huu')
  have hαL : mulAutOfLin ρ ∈ autOn L V := by
    rw [autOn_eq_top_of_hyp1281One h]
    exact Subgroup.mem_top _
  obtain ⟨⟨l, hlN⟩, hlL, hlα⟩ := hαL
  have hlL' : l ∈ L := Subgroup.mem_subgroupOf.1 hlL
  have hconj : ∀ x (hx : x ∈ V), l * x * l⁻¹ =
      ((Additive.toMul (ρ (Additive.ofMul ⟨x, hx⟩)) : ↥V) : G) := by
    intro x hx
    rw [← mulAutOfLin_apply, ← hlα]
    rfl
  have hpow : ∀ (m : ℕ) (x : G) (hx : x ∈ V), l ^ m * x * (l ^ m)⁻¹ =
      ((Additive.toMul ((ρ ^ m) (Additive.ofMul ⟨x, hx⟩)) : ↥V) : G) := by
    intro m
    induction m with
    | zero =>
      intro x hx
      simp
    | succ m ih =>
      intro x hx
      rw [show l ^ (m + 1) * x * (l ^ (m + 1))⁻¹ = l * (l ^ m * x * (l ^ m)⁻¹) * l⁻¹ by group,
        ih x hx, hconj _ (Additive.toMul ((ρ ^ m) (Additive.ofMul ⟨x, hx⟩))).2, pow_succ',
        LinearEquiv.mul_apply]
      rfl
  have hlV₁ : l ∈ Subgroup.normalizer (V₁ : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun x hx => ?_)
    have h1 := hconj x (hV₁.1 hx)
    rw [hρP _ ((hmem (Additive.ofMul ⟨x, hV₁.1 hx⟩)).2 hx), toMul_ofMul] at h1
    have h2 : l * x = x * l := by
      calc l * x = (l * x * l⁻¹) * l := by group
        _ = x * l := by rw [h1]
    exact h2.symm
  have hρ3' : ρ ^ 3 = 1 := LinearEquiv.ext fun x => by
    rw [pow_three, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact hρ3 x
  obtain ⟨k, m, hm3, hlo⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos l).ne' 3 (by norm_num)
  have hy3 : (l ^ m) ^ 3 ^ k = 1 := by
    rw [← pow_mul, mul_comm, ← hlo, pow_orderOf_eq_one]
  refine ⟨l ^ m, ?_, ⟨k, hy3⟩, ?_⟩
  · exact mem_oTwoUpper_of_odd ⟨L.pow_mem hlL' m, Subgroup.pow_mem _ hlV₁ m⟩
      (Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one hy3))
  · rw [hpow m u hu]
    have hred : ρ ^ m = ρ ^ (m % 3) := by
      conv_lhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, hρ3', one_pow, one_mul]
    have hm' : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases hm' with h1 | h2
    · rw [hred, h1, pow_one]
      show ((Additive.toMul (ρ a) : ↥V) : G) * u⁻¹ ∉ V₁
      rw [hρa, toMul_ofMul]
      exact huu'
    · rw [hred, h2, sq, LinearEquiv.mul_apply]
      show ((Additive.toMul (ρ (ρ a)) : ↥V) : G) * u⁻¹ ∉ V₁
      rw [hρa, hρb, toMul_sub, toMul_neg, toMul_ofMul, toMul_ofMul]
      intro hmem'
      apply hu'V₁
      have hcomm : u⁻¹ * u'⁻¹ = u'⁻¹ * u⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, hab u hu u' hu']
      have hu2 : u * u = 1 := by rw [← sq]; exact hsq u hu
      have e1 : (((⟨u, hu⟩ : ↥V)⁻¹ / ⟨u', hu'⟩ : ↥V) : G) * u⁻¹ = u'⁻¹ := by
        rw [Subgroup.coe_div, Subgroup.coe_inv, div_eq_mul_inv, hcomm, mul_assoc,
          ← mul_inv_rev, hu2, inv_one, mul_one]
      rw [e1] at hmem'
      simpa using V₁.inv_mem hmem'

theorem thirteen_four_three (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) {T L V : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}
    (hs : Setting1282One G T L V n V₁ V₂) (hn : n = 3) {g : G} (hg : g ∈ p128 T L V)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hZ : V₁ < zU128 V V₁) :
    ¬ CFSG.conjugate (zU128 V V₁) g ≤
      centralizerMod (zU128 V V₁) (Subgroup.normalizer (V₁ : Set G)) (u128 V V₁) := by
  classical
  intro hle
  have hyp := hs.hyp
  obtain ⟨k, hk, hkN, hkY⟩ := exists_conjugate_eq hyp hs.v1 hg hgN
  obtain ⟨-, hTZ⟩ := T_le_normalizer_w128 h1222 h12213 hs
  rw [hkY _ hTZ] at hle
  have S := setting128A h1222 h12213 hs
  have hUeq := uA_eq h1222 hs
  have hgood : L128A.Good V₁ (oTwoUpper (p128 T L V)) k := ⟨hk, hkN⟩
  have hUT : u128 V V₁ ≤ T := (hs.almostSpecial h1222 h12213).G22_three.1
  have hkZ : ∀ z ∈ zU128 V V₁, k⁻¹ * z * k ∈ u128 V V₁ := by
    intro z hz
    have hz' : k⁻¹ * z * k ∈ rconj (zU128 V V₁) k := by
      rw [mem_rconj]
      have e : k * (k⁻¹ * z * k) * k⁻¹ = z := by group
      rw [e]
      exact hz
    have h1 := hle hz'
    have h2 : k⁻¹ * z * k ∈ centralizerMod (centerOf (L128A.uA V₂ V₁))
        (rconj (L128A.wA V₂ V₁) k) (L128A.uA V₂ V₁) := by
      refine ⟨L128A.Setting.rconj_centerOf_le_rconj_wA V₂ V₁ k ?_, ?_, ?_⟩
      · rw [hUeq]
        exact hz'
      · rw [hUeq]
        exact h1.2.1
      · rw [hUeq]
        exact h1.2.2
    rw [(S.nine_five hgood).1] at h2
    exact hUeq ▸ h2.1.1
  obtain ⟨hZJ, -, -, hLTJ⟩ := sup_le_normalizer_centerOf_i128 h1222 h12213 hs hk hkN hkZ
  have hL₁C := lOne_le_centralizer_centerOf h1222 h12213 hs hk hkN hkZ
  set J := centerOf (i128 T L V V₁) with hJdef
  have hZJ' : zU128 V V₁ = J ⊔ V₁ := hZJ
  have hJZ : J ≤ zU128 V V₁ := hZJ' ▸ le_sup_left
  have hJne : J ≠ ⊥ := by
    intro hb
    rw [hb, bot_sup_eq] at hZJ'
    exact hZ.ne hZJ'.symm
  have hZU : zU128 V V₁ ≤ u128 V V₁ := fun z hz => hz.1
  have hJ2 : IsPGroup 2 J := hyp.hyp.sylow.1.to_le (hJZ.trans (hZU.trans hUT))
  have hNJ : Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    L1297.normalizer_le_of_sup_le h37 h38 h39 hyp.hyp hJne hJ2 hLTJ
  have hCM : Subgroup.centralizer (zU128 V V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    intro c hc
    apply hNJ
    exact mem_normalizer_of_conj_mem_of_finite fun w hw => by
      rw [← Subgroup.mem_centralizer_iff.1 hc w (hJZ hw), mul_inv_cancel_right]
      exact hw
  set H := Subgroup.normalizer (V₁ : Set G) with hHdef
  have hNZ : H ≤ Subgroup.normalizer (zU128 V V₁ : Set G) :=
    (le_normalizer_conjClosure V _).trans (normalizer_le_normalizer_centerOf _)
  have hL₁H : lOne L V₁ ≤ H := (oTwoUpper_le _).trans inf_le_right
  set JJ := conjClosure (lOne L V₁) H with hJJdef
  have hJJH : JJ ≤ H := conjClosure_le fun h hh l hl =>
    H.mul_mem (H.mul_mem hh (hL₁H hl)) (H.inv_mem hh)
  have hHJJ : H ≤ Subgroup.normalizer (JJ : Set G) := le_normalizer_conjClosure _ _
  have hJJC : JJ ≤ Subgroup.centralizer (zU128 V V₁ : Set G) := conjClosure_le fun h hh l hl =>
    (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_centralizer'' _ (hNZ hh)) l).1
      (hL₁C hl)
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hs.v1.2.1
  have hJJV : JJ ≤ Subgroup.normalizer (V : Set G) := by
    intro j hj
    rcases hyp.hyp.ti_of_1222 h1222 (hCM (hJJC hj)) with h | h
    · exact SteinbergBS.mem_normalizer_of_conjugate_eq h
    · exfalso
      have hle1 : V₁ ≤ V ⊓ CFSG.conjugate V j := le_inf hs.v1.1 fun x hx => by
        rw [SteinbergBS.mem_conjugate_iff]
        exact hs.v1.1 ((Subgroup.mem_normalizer_iff.1 (hJJH hj) x).1 hx)
      rw [h, le_bot_iff] at hle1
      rw [hle1, Subgroup.card_bot] at hV₁2
      norm_num at hV₁2
  have hJJVh : ∀ h ∈ H, JJ ≤ Subgroup.normalizer
      ((V.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G) := by
    intro h hh j hj
    refine mem_normalizer_of_conj_mem_of_finite fun x hx => ?_
    obtain ⟨v, hv, rfl⟩ := hx
    have hj' : h⁻¹ * j * h⁻¹⁻¹ ∈ JJ :=
      (Subgroup.mem_normalizer_iff.1 (hHJJ (H.inv_mem hh)) j).1 hj
    rw [inv_inv] at hj'
    refine ⟨h⁻¹ * j * h * v * (h⁻¹ * j * h)⁻¹,
      (Subgroup.mem_normalizer_iff.1 (hJJV hj') v).1 hv, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  obtain ⟨hcard, hsq, hab⟩ := hyp.card_sq
  have hV₁V₂ : V₁ < V₂ := lt_of_le_of_ne hs.le fun h => by
    have h1 := hs.v2.2.1
    rw [← h, hV₁2] at h1
    norm_num at h1
  obtain ⟨u, huV₂, huV₁⟩ := IsConcreteLE.exists_of_lt hV₁V₂
  have hV₂V : V₂ < V := lt_of_le_of_ne hs.v2.1 fun h => by
    have h1 := hs.v2.2.1
    rw [h, hcard, hn] at h1
    norm_num at h1
  obtain ⟨u', hu'V, hu'V₂⟩ := IsConcreteLE.exists_of_lt hV₂V
  have huV : u ∈ V := hs.v2.1 huV₂
  have huu : u * u'⁻¹ ∉ V₁ := fun h1 => hu'V₂ (by
    have h2 := V₂.mul_mem (V₂.inv_mem (hs.le h1)) huV₂
    rwa [show (u * u'⁻¹)⁻¹ * u = u' by group] at h2)
  obtain ⟨y, hyL₁, ⟨e, hye⟩, hyu⟩ :=
    exists_three_elt_lOne hyp hs.v1 huV hu'V huV₁ (fun h => hu'V₂ (hs.le h)) huu
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P'⟩ := (inferInstance : Nonempty (Sylow 3 ↥JJ))
  set P := (P' : Subgroup ↥JJ).map JJ.subtype with hPdef
  have hPJJ : P ≤ JJ := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hP3 : IsPGroup 3 ↥P := P'.isPGroup'.map JJ.subtype
  have hPodd : Odd (Nat.card ↥P) := by
    obtain ⟨r, hr⟩ := IsPGroup.iff_card.1 hP3
    rw [hr]
    exact Odd.pow (by decide)
  have hmove : ∀ h ∈ H, ∃ a ∈ P, Odd (orderOf a) ∧ ∃ x ∈ V.map (MulAut.conj h).toMonoidHom,
      a * x * a⁻¹ * x⁻¹ ∉ V₁ := by
    intro h hh
    have hyh : h * y * h⁻¹ ∈ JJ := mem_conjClosure hh hyL₁
    set yh : ↥JJ := ⟨h * y * h⁻¹, hyh⟩ with hyhdef
    have hyh3 : yh ^ 3 ^ e = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hyhdef, conj_pow, hye]
      simp
    have hY3 : IsPGroup 3 ↥(Subgroup.zpowers yh) := by
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hyh3)
      exact IsPGroup.of_card (by rw [Nat.card_zpowers, hi])
    obtain ⟨Q, hQ⟩ := hY3.exists_le_sylow
    obtain ⟨j, hj⟩ := MulAction.exists_smul_eq ↥JJ P' Q
    have hyQ : yh ∈ (Q : Subgroup ↥JJ) := hQ (Subgroup.mem_zpowers yh)
    rw [← hj, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hyQ
    obtain ⟨a', ha', hay⟩ := hyQ
    rw [MulAut.smul_def, MulAut.conj_apply] at hay
    have hay' : (a' : G) = (j : G)⁻¹ * (h * y * h⁻¹) * j := by
      have h1 := congrArg (fun x : ↥JJ => (x : G)) hay
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hyhdef] at h1
      rw [← h1]
      group
    have hjH : (j : G) ∈ H := hJJH j.2
    refine ⟨(a' : G), ⟨a', ha', rfl⟩, ?_, (j : G)⁻¹ * (h * u * h⁻¹) * j, ?_, ?_⟩
    · have hd : orderOf (a' : G) ∣ 3 ^ e := by
        apply orderOf_dvd_of_pow_eq_one
        have e2 : (j : G)⁻¹ * (h * y * h⁻¹) * j = ((j : G)⁻¹ * h) * y * ((j : G)⁻¹ * h)⁻¹ := by
          group
        rw [hay', e2, conj_pow, hye]
        group
      exact Odd.of_dvd_nat (Odd.pow (by decide)) hd
    · have h1 := (Subgroup.mem_normalizer_iff.1 (hJJVh h hh (JJ.inv_mem j.2))
        (h * u * h⁻¹)).1 ⟨u, huV, by simp [MulAut.conj_apply]⟩
      simpa using h1
    · intro hmem
      apply hyu
      have e1 : (a' : G) * ((j : G)⁻¹ * (h * u * h⁻¹) * j) * (a' : G)⁻¹ *
          ((j : G)⁻¹ * (h * u * h⁻¹) * j)⁻¹ =
          (j : G)⁻¹ * (h * (y * u * y⁻¹ * u⁻¹) * h⁻¹) * j := by
        rw [hay']
        group
      rw [e1] at hmem
      have h2 := (Subgroup.mem_normalizer_iff.1 hjH _).1 hmem
      have e2 : (j : G) * ((j : G)⁻¹ * (h * (y * u * y⁻¹ * u⁻¹) * h⁻¹) * j) * (j : G)⁻¹ =
          h * (y * u * y⁻¹ * u⁻¹) * h⁻¹ := by group
      rw [e2] at h2
      have h3 := (Subgroup.mem_normalizer_iff.1 (H.inv_mem hh) _).1 h2
      have e3 : h⁻¹ * (h * (y * u * y⁻¹ * u⁻¹) * h⁻¹) * h⁻¹⁻¹ = y * u * y⁻¹ * u⁻¹ := by group
      rwa [e3] at h3
  have hUN : u128 V V₁ ≤ Subgroup.normalizer (V₁ : Set G) := hUeq ▸ S.uA_le_normalizer
  have hUc : ∀ x ∈ u128 V V₁, ∀ y ∈ u128 V V₁, x * y * x⁻¹ * y⁻¹ ∈ V₁ := by
    intro x hx y hy
    rw [← hUeq] at hx hy
    exact S.commutator_mem hx hy
  have hUs : ∀ x ∈ u128 V V₁, x ^ 2 ∈ V₁ := by
    intro x hx
    rw [← hUeq] at hx
    exact S.sq_mem hx
  obtain ⟨z, hzZ, hzV₁⟩ := IsConcreteLE.exists_of_lt hZ
  apply hzV₁
  refine L128N.mem_of_fixed_of_norm {x | ∃ h ∈ H, ∃ v ∈ V, h * v * h⁻¹ = x} rfl
    (hs.v1.1.trans (le_conjClosure V H)) hUN hUc hUs
    (hPJJ.trans (hJJH.trans (le_normalizer_conjClosure V H))) (hPJJ.trans hJJH) hPodd ?_
    hzZ.1 ?_
  · rintro s ⟨h, hh, v, hv, rfl⟩
    have hWU : V.map (MulAut.conj h).toMonoidHom ≤ u128 V V₁ := by
      rintro _ ⟨v', hv', rfl⟩
      exact mem_conjClosure hh hv'
    refine ⟨V.map (MulAut.conj h).toMonoidHom, ⟨v, hv, rfl⟩, hWU, hPJJ.trans (hJJVh h hh), ?_⟩
    intro w hw hfix
    obtain ⟨a, haP, hodd, x, hx, hax⟩ := hmove h hh
    have hV₁W : V₁ ≤ V.map (MulAut.conj h).toMonoidHom := by
      intro x hx
      refine ⟨h⁻¹ * x * h, hs.v1.1 ?_, ?_⟩
      · have h1 := (Subgroup.mem_normalizer_iff.1 (H.inv_mem hh) x).1 hx
        rwa [inv_inv] at h1
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    have hcW : Nat.card (V.map (MulAut.conj h).toMonoidHom) = 8 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hcard, hn]
      norm_num
    exact L128N.mem_of_fixed_of_card_eight hV₁W (hWU.trans hUN) hcW hV₁2
      (fun x hx y hy => hUc x (hWU hx) y (hWU hy)) (fun x hx => hUs x (hWU hx))
      (hJJVh h hh (hPJJ haP)) (hJJH (hPJJ haP)) hodd hx hax hw (hfix a haP)
  · intro a ha
    have h1 := Subgroup.mem_centralizer_iff.1 (hJJC (hPJJ ha)) z hzZ
    rw [← h1, mul_inv_cancel_right, mul_inv_cancel]
    exact V₁.one_mem

end L128P

end CFSG.Quasithin.H13
