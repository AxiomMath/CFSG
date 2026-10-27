module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma6One
public import CFSG.GroupTheory.KleinFourAutomorphism

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative commutatorElement

namespace L1296

theorem exists_linearEquiv_extend_sub {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (U : Submodule K E) (e : U ≃ₗ[K] U) :
    ∃ β : E ≃ₗ[K] E, (∀ u : U, β u = e u) ∧ ∀ x, β x - x ∈ U := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl U
  set P := Submodule.prodEquivOfIsCompl U C hC with hP
  let β : E ≃ₗ[K] E := (P.symm.trans (e.prodCongr (LinearEquiv.refl K C))).trans P
  have hβ : ∀ (u : U) (c : C), β ((u : E) + c) = (e u : E) + c := by
    intro u c
    have h1 : (u : E) + c = P (u, c) := (Submodule.coe_prodEquivOfIsCompl' U C hC (u, c)).symm
    rw [h1]
    simp [β, P]
  refine ⟨β, fun u => ?_, fun x => ?_⟩
  · have := hβ u 0
    simpa using this
  · obtain ⟨⟨u, c⟩, rfl⟩ := P.surjective x
    rw [Submodule.coe_prodEquivOfIsCompl', hβ,
      show (e u : E) + c - ((u : E) + c) = (e u : E) - u by abel]
    exact U.sub_mem (e u).2 u.2

theorem succ_le_pRank_of_commute {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {E H : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) {r : ℕ} (hEcard : Nat.card E = p ^ r) {b : G}
    (hbc : ∀ e ∈ E, Commute e b) (hbp : b ^ p = 1) (hbE : b ∉ E) (hEH : E ≤ H)
    (hbH : b ∈ H) : r + 1 ≤ CFSG.Open.pRank p H := by
  have : Fact p.Prime := ⟨hp⟩
  have hb1 : b ≠ 1 := fun h => hbE (h ▸ one_mem E)
  have hbord : orderOf b = p := orderOf_eq_prime hbp hb1
  have hcomm : ∀ (e : E) (c : Subgroup.zpowers b),
      Commute (E.subtype e) ((Subgroup.zpowers b).subtype c) := by
    rintro e ⟨c, k, rfl⟩
    exact (hbc e e.2).zpow_right k
  let f : E × Subgroup.zpowers b →* G :=
    MonoidHom.noncommCoprod E.subtype (Subgroup.zpowers b).subtype hcomm
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨e, c⟩ hx
    have hx' : (e : G) * c = 1 := hx
    have hcE : (c : G) ∈ E := by
      rw [eq_inv_of_mul_eq_one_right hx']
      exact inv_mem e.2
    have hc1 : c = 1 := by
      by_contra hc
      have htop := zpowers_eq_top_of_prime_card (G := Subgroup.zpowers b)
        (by rw [Nat.card_zpowers, hbord]) hc
      have hbmem : (⟨b, Subgroup.mem_zpowers b⟩ : Subgroup.zpowers b) ∈ Subgroup.zpowers c :=
        htop ▸ Subgroup.mem_top _
      obtain ⟨m, hm⟩ := hbmem
      apply hbE
      have : (c : G) ^ m = b := congrArg Subtype.val hm
      rw [← this]
      exact zpow_mem hcE m
    rw [hc1, OneMemClass.coe_one, mul_one] at hx'
    have he1 : e = 1 := Subtype.ext hx'
    rw [he1, hc1]
    rfl
  have hEc := hE.1
  refine CFSG.SectionRank.le_pRank_of_injective hp.one_lt (A := E × Subgroup.zpowers b) ?_ ?_ ?_
    f hf ?_
  · rintro ⟨e₁, c₁⟩ ⟨e₂, c₂⟩
    refine Prod.ext (mul_comm' e₁ e₂) ?_
    obtain ⟨c₁, k₁, rfl⟩ := c₁
    obtain ⟨c₂, k₂, rfl⟩ := c₂
    exact Subtype.ext (Commute.zpow_zpow_self b k₁ k₂).eq
  · rintro ⟨e, c⟩
    refine Prod.ext (Subtype.ext (hE.2 e e.2)) ?_
    obtain ⟨c, k, rfl⟩ := c
    apply Subtype.ext
    change (b ^ k) ^ p = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hbp, one_zpow]
  · rw [Nat.card_prod, hEcard, Nat.card_zpowers, hbord, pow_succ]
  · rintro _ ⟨⟨e, c⟩, rfl⟩
    obtain ⟨c, k, rfl⟩ := c
    exact H.mul_mem (hEH e.2) (zpow_mem hbH k)

variable {G : Type} [Group G]

theorem isKleinFour_of_card {W : Subgroup G} (hW : Nat.card W = 4) (hsq : ∀ w ∈ W, w ^ 2 = 1) :
    IsKleinFour ↥W := by
  refine ⟨hW, ?_⟩
  have hdvd : Monoid.exponent ↥W ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun w => Subtype.ext (by simpa using hsq _ w.2)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exfalso
    have : Finite ↥W := Nat.finite_of_card_ne_zero (by rw [hW]; norm_num)
    have : Nontrivial ↥W := Finite.one_lt_card_iff_nontrivial.1 (by rw [hW]; norm_num)
    obtain ⟨w, hw⟩ := exists_ne (1 : ↥W)
    apply hw
    have := Monoid.pow_exponent_eq_one w
    rwa [h1, pow_one] at this
  · exact h2

theorem false_of_normal_card_two (E : Type) [Group E] [IsKleinFour E] {H : Subgroup (MulAut E)}
    (hN : H.Normal) (h2 : Nat.card H = 2) : False := by
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [IsKleinFour.card_four]; norm_num)
  have : Finite (MulAut E) :=
    Finite.of_injective (fun f : MulAut E => (f : E → E)) DFunLike.coe_injective
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ H, a ≠ 1 := by
    by_contra hne
    push Not at hne
    have hbot : H = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hne
    rw [hbot, Subgroup.card_bot] at h2
    norm_num at h2
  have hc : ∀ b : MulAut E, b * a = a * b := by
    intro b
    have h1 := Subgroup.mem_centralizer_iff.1 (le_centralizer_normalizer_of_card_eq_two h2 ha) b
      (by rw [Subgroup.normalizer_eq_top_iff.2 hN]; exact Subgroup.mem_top b)
    exact h1
  set φ := CFSG.kleinFourAutomorphismEquivSymmetricThree E with hφ
  have key : ∀ σ : Equiv.Perm (Fin 3), σ ≠ 1 → ∃ τ : Equiv.Perm (Fin 3), τ * σ ≠ σ * τ := by
    decide
  obtain ⟨τ, hτ⟩ := key (φ a) (fun h => ha1 (φ.injective (by rw [h, map_one])))
  apply hτ
  have := congrArg φ (hc (φ.symm τ))
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this

theorem eq_top_of_normal_of_orderOf (E : Type) [Group E] [IsKleinFour E] {H : Subgroup (MulAut E)}
    (hN : H.Normal) {a : MulAut E} (ha : a ∈ H) (ha2 : orderOf a = 2) : H = ⊤ := by
  rcases CFSG.kleinFour_automorphism_subgroup_card E H a ha ha2 with h2 | h6
  · exact (false_of_normal_card_two E hN h2).elim
  · exact CFSG.kleinFour_automorphism_subgroup_eq_top_of_card_six E H h6

theorem eq_bot_of_normal_of_isPGroup (E : Type) [Group E] [IsKleinFour E]
    {H : Subgroup (MulAut E)} (hN : H.Normal) (hp : IsPGroup 2 H) : H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [IsKleinFour.card_four]; norm_num)
  have : Finite (MulAut E) :=
    Finite.of_injective (fun f : MulAut E => (f : E → E)) DFunLike.coe_injective
  by_contra hne
  have hnt : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hne
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.2 hnt).ne' hk
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := H) 2 (by rw [hk]; exact dvd_pow_self 2 hk0)
  have htop := eq_top_of_normal_of_orderOf E hN a.2 (by rw [Subgroup.orderOf_coe, ha])
  have h6 := CFSG.kleinFour_automorphism_card E
  rw [htop, Subgroup.card_top, h6] at hk
  have h1 : (2 : ℕ) ^ k ≠ 6 := by
    intro h
    have : 3 ∣ 2 ^ k := by rw [h]; norm_num
    exact absurd ((Nat.Prime.dvd_of_dvd_pow Nat.prime_three) this) (by norm_num)
  exact h1 hk.symm

theorem autOn_le_normalizer {X M V : Subgroup G} (hMX : M ≤ Subgroup.normalizer (X : Set G)) :
    autOn M V ≤ Subgroup.normalizer (autOn X V : Set (MulAut ↥V)) :=
  CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn hMX

theorem conjAct_mem_autOn {X V : Subgroup G} {x : G} (hxX : x ∈ X)
    (hxN : x ∈ Subgroup.normalizer (V : Set G)) : conjAct V ⟨x, hxN⟩ ∈ autOn X V :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hxX)

theorem le_p128 {T L V : Subgroup G} : T ≤ p128 T L V := fun t ht =>
  Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_right ht, Subgroup.mem_iInf.2 fun _ =>
    Subgroup.mem_iInf.2 fun hY => by
      obtain ⟨i, -, hYi⟩ := hY
      exact hYi.2.2 ht⟩

theorem p128_le_normalizer {T L V Y : Subgroup G} {i : ℕ} (hi : 2 ≤ i) (hY : IsTSub T V Y i) :
    p128 T L V ≤ Subgroup.normalizer (Y : Set G) := fun _ hp =>
  Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hp).2 Y) ⟨i, hi, hY⟩

variable [Finite G]

theorem le_of_isTSub (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₂ Y : Subgroup G} (hV₂ : IsTSub T V V₂ 2) {i : ℕ} (hi : 2 ≤ i)
    (hY : IsTSub T V Y i) : V₂ ≤ Y := by
  rcases tinv_comparable_of_hyp1281One h1222 h hV₂.1 hY.1 hV₂.2.2 hY.2.2 with hle | hle
  · exact hle
  · have heq : Y = V₂ := Subgroup.eq_of_le_of_card_ge hle (by
      rw [hV₂.2.1, hY.2.1]
      exact Nat.pow_le_pow_right (by norm_num) hi)
    rw [heq]

theorem exists_mem_p128 (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₂ : Subgroup G} (hV₂ : IsTSub T V V₂ 2) (α : MulAut ↥V₂) :
    ∃ p ∈ p128 T L V, ∀ x (hx : x ∈ V₂), p * x * p⁻¹ = ((α ⟨x, hx⟩ : ↥V₂) : G) := by
  obtain ⟨-, hsq, -⟩ := h.card_sq
  obtain ⟨hc, -⟩ := h.natural
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.hyp.irrPlus.2.2.1
  have hV₂V := hV₂.1
  let _ := zmodModuleOf hsq
  let cj : MulAut ↥V₂ → (subOf (V := V) V₂ →+ subOf (V := V) V₂) := fun a =>
    { toFun := fun x => ⟨Additive.ofMul ⟨((a ⟨((Additive.toMul (x : Additive ↥V) : ↥V) : G),
          mem_subOf.1 x.2⟩ : ↥V₂) : G), hV₂V (a _).2⟩, mem_subOf.2 (a _).2⟩
      map_zero' := by
        apply Subtype.ext
        apply Additive.toMul.injective
        apply Subtype.ext
        show ((a 1 : ↥V₂) : G) = 1
        rw [map_one, OneMemClass.coe_one]
      map_add' := fun x y => by
        apply Subtype.ext
        apply Additive.toMul.injective
        apply Subtype.ext
        show ((a (⟨((Additive.toMul (x : Additive ↥V) : ↥V) : G), mem_subOf.1 x.2⟩ *
          ⟨((Additive.toMul (y : Additive ↥V) : ↥V) : G), mem_subOf.1 y.2⟩) : ↥V₂) : G) = _
        rw [map_mul]
        rfl }
  have hcj : ∀ (a : MulAut ↥V₂) (x : subOf (V := V) V₂),
      ((Additive.toMul ((cj a x : subOf (V := V) V₂) : Additive ↥V) : ↥V) : G) =
        ((a ⟨((Additive.toMul (x : Additive ↥V) : ↥V) : G), mem_subOf.1 x.2⟩ : ↥V₂) : G) :=
    fun _ _ => rfl
  let e : subOf (V := V) V₂ ≃ₗ[ZMod 2] subOf (V := V) V₂ :=
    LinearEquiv.ofLinearMap ((cj α).toZModLinearMap 2) ((cj α⁻¹).toZModLinearMap 2)
      (by
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        apply Additive.toMul.injective
        apply Subtype.ext
        show ((α (α⁻¹ ⟨((Additive.toMul (x : Additive ↥V) : ↥V) : G), mem_subOf.1 x.2⟩) :
          ↥V₂) : G) = _
        rw [MulAut.apply_inv_self]
        rfl)
      (by
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        apply Additive.toMul.injective
        apply Subtype.ext
        show ((α⁻¹ (α ⟨((Additive.toMul (x : Additive ↥V) : ↥V) : G), mem_subOf.1 x.2⟩) :
          ↥V₂) : G) = _
        rw [MulAut.inv_apply_self]
        rfl)
  obtain ⟨β, hβ, hβsub⟩ := exists_linearEquiv_extend_sub (subOf (V := V) V₂) e
  have hαL : mulAutOfLin β ∈ autOn L V := by
    rw [autOn_eq_top_of_hyp1281One h]
    exact Subgroup.mem_top _
  obtain ⟨⟨l, hlN⟩, hlL, hlα⟩ := hαL
  have hlL' : l ∈ L := Subgroup.mem_subgroupOf.1 hlL
  have hconj : ∀ x (hx : x ∈ V), l * x * l⁻¹ =
      ((Additive.toMul (β (Additive.ofMul ⟨x, hx⟩)) : ↥V) : G) := by
    intro x hx
    have e1 : l * x * l⁻¹ = ((mulAutOfLin β ⟨x, hx⟩ : ↥V) : G) := by
      rw [← hlα]
      rfl
    rw [e1, mulAutOfLin_apply]
  have hsub : ∀ x (hx : x ∈ V), l * x * l⁻¹ * x⁻¹ ∈ V₂ := by
    intro x hx
    have h1 := mem_subOf.1 (hβsub (Additive.ofMul ⟨x, hx⟩))
    simp only [toMul_sub, toMul_ofMul, Subgroup.coe_div] at h1
    rw [← hconj x hx, div_eq_mul_inv] at h1
    exact h1
  refine ⟨l, Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_left hlL', Subgroup.mem_iInf.2 fun Y =>
    Subgroup.mem_iInf.2 fun hY => ?_⟩, fun x hx => ?_⟩
  · obtain ⟨i, hi, hYi⟩ := hY
    have hV₂Y := le_of_isTSub h1222 h hV₂ hi hYi
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hyV := hYi.1 hy
      have h1 : l * y * l⁻¹ * y⁻¹ ∈ Y := hV₂Y (hsub y hyV)
      have h2 := Y.mul_mem h1 hy
      rwa [inv_mul_cancel_right] at h2
    · intro hy
      have hyV : y ∈ V := by
        have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hlN) _).1 (hYi.1 hy)
        rwa [show l⁻¹ * (l * y * l⁻¹) * l⁻¹⁻¹ = y by group] at h1
      have h1 : l * y * l⁻¹ * y⁻¹ ∈ Y := hV₂Y (hsub y hyV)
      have h2 := Y.mul_mem (Y.inv_mem h1) hy
      rwa [show (l * y * l⁻¹ * y⁻¹)⁻¹ * (l * y * l⁻¹) = y by group] at h2
  · rw [hconj x (hV₂V hx), hβ ⟨Additive.ofMul ⟨x, hV₂V hx⟩, mem_subOf.2 hx⟩]
    exact hcj α _

theorem autOn_p128_eq_top (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₂ : Subgroup G} (hV₂ : IsTSub T V V₂ 2) :
    autOn (p128 T L V) V₂ = ⊤ := by
  refine eq_top_iff.2 fun α _ => ?_
  obtain ⟨p, hp, hpα⟩ := exists_mem_p128 h1222 h hV₂ α
  have hpN : p ∈ Subgroup.normalizer (V₂ : Set G) := p128_le_normalizer le_rfl hV₂ hp
  refine Subgroup.mem_map.2 ⟨⟨p, hpN⟩, Subgroup.mem_subgroupOf.2 hp, ?_⟩
  ext x
  rw [A1b.conjAct_coe]
  exact hpα x.1 x.2

theorem isPGroup_p128_inf_centralizer (h1222 : Stmt12_2_2) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₂ : Subgroup G} (hV₂ : IsTSub T V V₂ 2) :
    IsPGroup 2 ↥(p128 T L V ⊓ Subgroup.centralizer (V₂ : Set G)) := by
  obtain ⟨hcard, hsq, hab⟩ := h.card_sq
  obtain ⟨-, hTV⟩ := h.hyp.le_and_normalizes h1222
  have hT2 : IsPGroup 2 T := h.hyp.sylow.1
  have hn2 : 2 ≤ n := by rcases h.n_mem with rfl | rfl | rfl <;> omega
  intro x
  obtain ⟨hxP, hxC⟩ := x.2
  have key : ∀ i, 2 ≤ i → i ≤ n → ∀ W : Subgroup G, IsTSub T V W i →
      (x : G) ^ (2 ^ (i - 2)) ∈ Subgroup.centralizer (W : Set G) := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base =>
      intro _ W hW
      have hle := le_of_isTSub h1222 h hV₂ le_rfl hW
      have heq : W = V₂ := (Subgroup.eq_of_le_of_card_ge hle (by rw [hV₂.2.1, hW.2.1])).symm
      rw [heq, show 2 - 2 = 0 by rfl, pow_zero, pow_one]
      exact hxC
    | succ i hi ih =>
      intro hin W' hW'
      obtain ⟨W, hW⟩ := exists_tsub hT2 hsq hab hTV hcard i (by omega)
      have hWW' : W ≤ W' := by
        rcases tinv_comparable_of_hyp1281One h1222 h hW.1 hW'.1 hW.2.2 hW'.2.2 with hle | hle
        · exact hle
        · exfalso
          have h1 := Subgroup.card_le_of_le hle
          rw [hW.2.1, hW'.2.1] at h1
          have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
          omega
      have hyC := ih (by omega) W hW
      set y := (x : G) ^ (2 ^ (i - 2)) with hy
      have hyW : y ∈ Subgroup.normalizer (W : Set G) :=
        Subgroup.pow_mem _ (p128_le_normalizer hi hW hxP) _
      have hyW' : y ∈ Subgroup.normalizer (W' : Set G) :=
        Subgroup.pow_mem _ (p128_le_normalizer (by omega) hW' hxP) _
      have hidx' : W.relIndex W' = 2 := by
        have h1 := Subgroup.relIndex_mul_card W W'
        rw [inf_eq_left.2 hWW', hW.2.1, hW'.2.1, pow_succ] at h1
        have h2 : 0 < 2 ^ i := by positivity
        have h3 : W.relIndex W' * 2 ^ i = 2 * 2 ^ i := by rw [h1, mul_comm]
        exact Nat.eq_of_mul_eq_mul_right h2 h3
      have hidx : (W.subgroupOf W').index = 2 := hidx'
      have hpow : (x : G) ^ (2 ^ (i + 1 - 2)) = y * y := by
        rw [hy, ← pow_add, show i + 1 - 2 = (i - 2) + 1 by omega, pow_succ, mul_two]
      rw [hpow, Subgroup.mem_centralizer_iff]
      intro w hw
      by_cases hwW : w ∈ W
      · have h1 := Subgroup.mem_centralizer_iff.1 hyC w hwW
        calc w * (y * y) = (w * y) * y := by group
          _ = (y * w) * y := by rw [h1]
          _ = y * (w * y) := by group
          _ = y * (y * w) := by rw [h1]
          _ = y * y * w := by group
      ·
        have hyw : y * w * y⁻¹ ∈ W' := (Subgroup.mem_normalizer_iff.1 hyW' w).1 hw
        have hywW : y * w * y⁻¹ ∉ W := fun h1 => hwW ((Subgroup.mem_normalizer_iff.1 hyW w).2 h1)
        have hc : y * w * y⁻¹ * w⁻¹ ∈ W := by
          have h1 := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨_, hyw⟩)
            (b := ⟨w⁻¹, W'.inv_mem hw⟩)).2
            (iff_of_false (fun h => hywW (Subgroup.mem_subgroupOf.1 h))
              (fun h => hwW (by simpa using Subgroup.mem_subgroupOf.1 h)))
          exact Subgroup.mem_subgroupOf.1 h1
        set c := y * w * y⁻¹ * w⁻¹ with hcdef
        have hyc : y * c * y⁻¹ = c := by
          have h1 := Subgroup.mem_centralizer_iff.1 hyC c hc
          rw [← h1, mul_inv_cancel_right]
        have hcc : c * c = 1 := by rw [← sq]; exact hsq _ (hW.1 hc)
        have hyw' : y * w * y⁻¹ = c * w := by rw [hcdef]; group
        have key2 : y * y * w * (y * y)⁻¹ = w := by
          calc y * y * w * (y * y)⁻¹ = y * (y * w * y⁻¹) * y⁻¹ := by group
            _ = y * (c * w) * y⁻¹ := by rw [hyw']
            _ = (y * c * y⁻¹) * (y * w * y⁻¹) := by group
            _ = c * (c * w) := by rw [hyc, hyw']
            _ = w := by rw [← mul_assoc, hcc, one_mul]
        calc w * (y * y) = (y * y * w * (y * y)⁻¹) * (y * y) := by rw [key2]
          _ = y * y * w := by group
  have hVn : IsTSub T V V n := ⟨le_rfl, hcard, hTV⟩
  have hxV := key n hn2 le_rfl V hVn
  have hxLT : (x : G) ^ (2 ^ (n - 2)) ∈ L ⊔ T :=
    Subgroup.pow_mem _ (Subgroup.mem_inf.1 hxP).1 _
  have hQ := (inf_centralizer_eq_sup_inf_centralizer h1222 h).1
  have hxQ : (x : G) ^ (2 ^ (n - 2)) ∈ T ⊓ Subgroup.centralizer (V : Set G) := by
    rw [hQ]
    exact ⟨hxLT, hxV⟩
  obtain ⟨m, hm⟩ := (hT2.to_le inf_le_left) ⟨_, hxQ⟩
  refine ⟨n - 2 + m, Subtype.ext ?_⟩
  have h1 := congrArg Subtype.val hm
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1 ⊢
  rw [pow_add, pow_mul]
  exact h1

end L1296


variable {G : Type} [Group G] [Finite G]

theorem lemma12_9_6_of (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h1295 : Lemma12_9_5) (hKG : ParabolicFact1296) : Lemma12_9_6 := by
  intro G _ _ T L V n hcx V₁ V₂ K₁ hV₁ hV₂ hV₁₂ hLK hK
  have h := hcx.hyp
  have hyp := h.hyp
  have hn : n ≠ 3 := by rcases hcx.n45 with h | h <;> omega
  obtain ⟨-, hsq, -⟩ := h.card_sq
  have hT2 : IsPGroup 2 T := hyp.sylow.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne₁ := commutator_ne_bot_of_cx h1222 h37 h38 h39 h1295 hKG hcx hV₁ hV₂ hV₁₂ hLK hK
  set G₁ := Subgroup.normalizer (V₁ : Set G) with hG₁
  set G₂ := Subgroup.normalizer (V₂ : Set G) with hG₂
  set R := pCoreOf 2 G₁ with hR
  set I₂ := conjClosure R G₂ with hI₂
  set P := p128 T L V with hP
  have hsq₂ : ∀ w ∈ V₂, w ^ 2 = 1 := fun w hw => hsq w (hV₂.1 hw)
  have : IsKleinFour ↥V₂ := L1296.isKleinFour_of_card (by rw [hV₂.2.1]; norm_num) hsq₂
  have hCG₁ : Subgroup.centralizer (V₂ : Set G) ≤ G₁ :=
    (Subgroup.centralizer_le hV₁₂).trans (Subgroup.centralizer_le_normalizer _)
  have hG₁R : G₁ ≤ Subgroup.normalizer (R : Set G) := LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hRT : R ≤ T :=
    L1296.le_of_isPGroup hyp.sylow (LieType.BorelTits.pCoreOf_isPGroup 2 _) (hV₁.2.2.trans hG₁R)
  have hTP : T ≤ P := L1296.le_p128
  have hPG₂ : P ≤ G₂ := L1296.p128_le_normalizer le_rfl hV₂
  have hG₂C : G₂ ≤ Subgroup.normalizer (Subgroup.centralizer (V₂ : Set G) : Set G) :=
    normalizer_le_normalizer_centralizer' V₂
  have hfac : ∀ g ∈ G₂, ∃ p ∈ P, p⁻¹ * g ∈ Subgroup.centralizer (V₂ : Set G) := by
    intro g hg
    obtain ⟨p, hp, hpg⟩ := L1296.exists_mem_p128 h1222 h hV₂ (conjAct V₂ ⟨g, hg⟩)
    refine ⟨p, hp, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    have h1 : p * x * p⁻¹ = g * x * g⁻¹ := by rw [hpg x hx, A1b.conjAct_coe]
    calc x * (p⁻¹ * g) = p⁻¹ * (p * x * p⁻¹) * g := by group
      _ = p⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
      _ = p⁻¹ * g * x := by group
  have hIP : I₂ ≤ P := by
    refine conjClosure_le fun g hg z hz => ?_
    obtain ⟨p, hp, hc⟩ := hfac g hg
    have hcz : (p⁻¹ * g) * z * (p⁻¹ * g)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.1 (hG₁R (hCG₁ hc)) z).1 hz
    rw [show g * z * g⁻¹ = p * ((p⁻¹ * g) * z * (p⁻¹ * g)⁻¹) * p⁻¹ by group]
    exact P.mul_mem (P.mul_mem hp (hTP (hRT hcz))) (P.inv_mem hp)
  have hIG₂ : I₂ ≤ G₂ := hIP.trans hPG₂
  have hG₂I : G₂ ≤ Subgroup.normalizer (I₂ : Set G) := le_normalizer_conjClosure R G₂
  have hPCp := L1296.isPGroup_p128_inf_centralizer h1222 h hV₂
  have hPCT : P ⊓ Subgroup.centralizer (V₂ : Set G) ≤ T := by
    refine L1296.le_of_isPGroup hyp.sylow hPCp fun t ht => ?_
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hTP ht),
      hG₂C (hV₂.2.2 ht)⟩
  have hAG₂ : autOn G₂ V₂ = ⊤ := eq_top_iff.2 ((L1296.autOn_p128_eq_top h1222 h hV₂).symm.le.trans
    (A4.autOn_mono hPG₂))
  have hAInorm : (autOn I₂ V₂).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hAG₂]
    exact L1296.autOn_le_normalizer hG₂I
  have hO₂K₁R : pCoreOf 2 K₁ ≤ R := by
    have hK₁n := normalizer_le_of_lOne_le h1222 h37 h38 h hn hV₁ hLK hK
    have hK₁G₁ : K₁ ≤ G₁ := le_of_mem_cComp (show K₁ ∈ cComp _ from hK)
    exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((LieType.BorelTits.pCoreOf_le 2 K₁).trans hK₁G₁)
      (hK₁n.trans (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₁))
      (LieType.BorelTits.pCoreOf_isPGroup 2 K₁)
  obtain ⟨r, hrR, hrC⟩ : ∃ r ∈ R, r ∉ Subgroup.centralizer (V₂ : Set G) := by
    by_contra hall
    push Not at hall
    apply hne₁
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
    exact fun x hx => hall x (hO₂K₁R hx)
  have hrG₂ : r ∈ G₂ := hIG₂ (le_conjClosure R G₂ hrR)
  set a := conjAct V₂ ⟨r, hrG₂⟩ with ha
  have haI : a ∈ autOn I₂ V₂ := L1296.conjAct_mem_autOn (le_conjClosure R G₂ hrR) hrG₂
  have ha1 : a ≠ 1 := fun h1 => hrC (A4.conjAct_eq_one_iff.1 h1)
  obtain ⟨k, hk⟩ := (LieType.BorelTits.pCoreOf_isPGroup 2 G₁) ⟨r, hrR⟩
  have hak : a ^ 2 ^ k = 1 := by
    have h1 : (⟨r, hrG₂⟩ : ↥G₂) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [ha, ← map_pow, h1, map_one]
  have hao : orderOf a ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hak
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hao
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact ha1 hj
  have h2a : 2 ∣ orderOf a := by rw [hj]; exact dvd_pow_self 2 hj0
  have hb := orderOf_pow_orderOf_div (x := a) (by rw [hj]; positivity) h2a
  have hAtop : autOn I₂ V₂ = ⊤ :=
    L1296.eq_top_of_normal_of_orderOf ↥V₂ hAInorm (Subgroup.pow_mem _ haI _) hb
  have hICp : IsPGroup 2 ↥(I₂ ⊓ Subgroup.centralizer (V₂ : Set G)) :=
    hPCp.to_le (inf_le_inf_right _ hIP)
  have hO₂C : pCoreOf 2 I₂ ≤ Subgroup.centralizer (V₂ : Set G) := by
    have hnorm : (autOn (pCoreOf 2 I₂) V₂).Normal := by
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hAtop]
      exact L1296.autOn_le_normalizer (LieType.BorelTits.le_normalizer_pCoreOf 2 I₂)
    have hbot := L1296.eq_bot_of_normal_of_isPGroup ↥V₂ hnorm
      (isPGroup_autOn (LieType.BorelTits.pCoreOf_isPGroup 2 I₂))
    intro x hx
    have hxN : x ∈ G₂ := hIG₂ (LieType.BorelTits.pCoreOf_le 2 I₂ hx)
    have h1 : conjAct V₂ ⟨x, hxN⟩ ∈ autOn (pCoreOf 2 I₂) V₂ := L1296.conjAct_mem_autOn hx hxN
    rw [hbot, Subgroup.mem_bot] at h1
    exact A4.conjAct_eq_one_iff.1 h1
  have hO₂eq : pCoreOf 2 I₂ = I₂ ⊓ Subgroup.centralizer (V₂ : Set G) := by
    refine le_antisymm (le_inf (LieType.BorelTits.pCoreOf_le 2 I₂) hO₂C) ?_
    refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ hICp
    exact fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, hG₂C (hIG₂ hx)⟩
  let ρ : ↥I₂ →* MulAut ↥V₂ := (conjAct V₂).comp (Subgroup.inclusion hIG₂)
  have hρ : ∀ x : ↥I₂, ρ x = 1 ↔ (x : G) ∈ Subgroup.centralizer (V₂ : Set G) := fun x =>
    A4.conjAct_eq_one_iff
  have hρs : Function.Surjective ρ := by
    intro α
    have hα : α ∈ autOn I₂ V₂ := by rw [hAtop]; exact Subgroup.mem_top α
    obtain ⟨⟨y, hyN⟩, hyI, rfl⟩ := Subgroup.mem_map.1 hα
    exact ⟨⟨y, Subgroup.mem_subgroupOf.1 hyI⟩, rfl⟩
  have hker : ρ.ker = CFSG.pCore 2 ↥I₂ := by
    ext x
    rw [MonoidHom.mem_ker, hρ]
    constructor
    · intro hx
      have h1 : (x : G) ∈ pCoreOf 2 I₂ := by rw [hO₂eq]; exact ⟨x.2, hx⟩
      obtain ⟨y, hy, hyx⟩ := h1
      rwa [← Subtype.ext hyx]
    · intro hx
      exact hO₂C ⟨x, hx, rfl⟩
  have hiso : Nonempty (↥I₂ ⧸ CFSG.pCore 2 ↥I₂ ≃* Equiv.Perm (Fin 3)) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρs)).trans
        (CFSG.kleinFourAutomorphismEquivSymmetricThree ↥V₂)⟩
  have hIT : I₂ ⊔ T = P := by
    refine le_antisymm (sup_le hIP hTP) fun x hx => ?_
    have hxN : x ∈ G₂ := hPG₂ hx
    have hα : conjAct V₂ ⟨x, hxN⟩ ∈ autOn I₂ V₂ := by rw [hAtop]; exact Subgroup.mem_top _
    obtain ⟨⟨y, hyN⟩, hyI, hyx⟩ := Subgroup.mem_map.1 hα
    have hyI' : y ∈ I₂ := Subgroup.mem_subgroupOf.1 hyI
    have hc : y⁻¹ * x ∈ Subgroup.centralizer (V₂ : Set G) := by
      have h1 : conjAct V₂ (⟨y, hyN⟩⁻¹ * ⟨x, hxN⟩) = 1 := by
        rw [map_mul, map_inv, hyx, inv_mul_cancel]
      exact A4.conjAct_eq_one_iff.1 h1
    have hcT : y⁻¹ * x ∈ T := hPCT ⟨P.mul_mem (P.inv_mem (hIP hyI')) hx, hc⟩
    rw [show x = y * (y⁻¹ * x) by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hyI') (Subgroup.mem_sup_right hcT)
  refine ⟨hne₁, ⟨hG₂I, hiso, hO₂eq, hIT⟩, ?_⟩
  obtain ⟨E, hEC, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3)
    (Subgroup.centralizer (V₂ : Set G))
  set kE := CFSG.Open.pRank 3 (Subgroup.centralizer (V₂ : Set G)) with hkE
  have h3I : 3 ∣ Nat.card ↥I₂ := by
    obtain ⟨e⟩ := hiso
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥I₂),
      Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    exact Dvd.dvd.mul_right (by decide) _
  obtain ⟨y, hy3⟩ := exists_prime_orderOf_dvd_card' (G := ↥I₂) 3 h3I
  have hy3' : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe, hy3]
  have hyC : (y : G) ∉ Subgroup.centralizer (V₂ : Set G) := by
    intro hyC
    obtain ⟨m, hm⟩ := hICp ⟨y, y.2, hyC⟩
    have h1 : orderOf (y : G) ∣ 2 ^ m := by
      refine orderOf_dvd_of_pow_eq_one ?_
      simpa using congrArg Subtype.val hm
    rw [hy3'] at h1
    exact absurd ((Nat.Prime.dvd_of_dvd_pow Nat.prime_three) h1) (by norm_num)
  set N := I₂ ⊓ Subgroup.centralizer (V₂ : Set G) with hNdef
  have hNG₂ : N ≤ G₂ := inf_le_left.trans hIG₂
  have hG₂N : G₂ ≤ Subgroup.normalizer (N : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hG₂I hg, hG₂C hg⟩
  have : (N.subgroupOf G₂).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNG₂).2 hG₂N
  set π := QuotientGroup.mk' (N.subgroupOf G₂) with hπ
  have hπ1 : ∀ x : ↥G₂, π x = 1 ↔ (x : G) ∈ N := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hEG₂ : E ≤ G₂ := hEC.trans (Subgroup.centralizer_le_normalizer _)
  set E' := E.subgroupOf G₂ with hE'
  have hE'e : IsElemAbelian 3 E' := by
    have := hE.1
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · have h1 := congrArg Subtype.val (mul_comm (⟨((a : ↥G₂) : G), a.2⟩ : ↥E)
        ⟨((b : ↥G₂) : G), b.2⟩)
      simpa using h1
    · simpa using hE.2 _ (Subgroup.mem_subgroupOf.1 hx)
  have hEN : ∀ x ∈ E, x ∈ N → x = 1 := by
    intro x hxE hxN
    obtain ⟨m, hm⟩ := hICp ⟨x, hxN⟩
    have h1 : orderOf x ∣ 2 ^ m :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hm)
    have h2 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (hE.2 x hxE)
    have h3 : orderOf x ∣ Nat.gcd 3 (2 ^ m) := Nat.dvd_gcd h2 h1
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right _ (by norm_num))] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  have hπinj : Function.Injective (π.domRestrict E') := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : π (x : ↥G₂) = 1 := hx
    rw [hπ1] at h1
    exact Subtype.ext (Subtype.ext (hEN _ (Subgroup.mem_subgroupOf.1 x.2) h1))
  have hĒcard : Nat.card ↥(E'.map π) = 3 ^ kE := by
    rw [← MonoidHom.domRestrict_range, ← Nat.card_congr (MonoidHom.ofInjective hπinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEG₂).toEquiv, hEcard]
  have hĒ : IsElemAbelian 3 (E'.map π) := CFSG.SectionRank.isElemAbelian_map hE'e π
  set yb := π ⟨y, hIG₂ y.2⟩ with hyb
  have hyb3 : yb ^ 3 = 1 := by
    have hy3e : (y : G) ^ 3 = 1 := by rw [← hy3']; exact pow_orderOf_eq_one _
    have h1 : (⟨(y : G), hIG₂ y.2⟩ : ↥G₂) ^ 3 = 1 := Subtype.ext (by simpa using hy3e)
    rw [hyb, ← map_pow, h1, map_one]
  have hybE : yb ∉ E'.map π := by
    rintro ⟨e, he, hey⟩
    have h1 : π (e⁻¹ * ⟨y, hIG₂ y.2⟩) = 1 := by rw [map_mul, map_inv, hey, ← hyb, inv_mul_cancel]
    rw [hπ1] at h1
    apply hyC
    have h2 := (Subgroup.mem_inf.1 h1).2
    have heC : ((e : ↥G₂) : G) ∈ Subgroup.centralizer (V₂ : Set G) :=
      hEC (Subgroup.mem_subgroupOf.1 he)
    have h3 := Subgroup.mul_mem _ heC h2
    simpa using h3
  have hybC : yb ∈ Subgroup.centralizer ((E'.map π : Subgroup _) : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨e, he, rfl⟩
    have heC : ((e : ↥G₂) : G) ∈ Subgroup.centralizer (V₂ : Set G) :=
      hEC (Subgroup.mem_subgroupOf.1 he)
    have hcomm : (y : G) * e * (y : G)⁻¹ * (e : G)⁻¹ ∈ N := by
      refine ⟨?_, ?_⟩
      · rw [show (y : G) * e * (y : G)⁻¹ * (e : G)⁻¹ = (y : G) * (e * (y : G)⁻¹ * (e : G)⁻¹) by
          group]
        exact I₂.mul_mem y.2 ((Subgroup.mem_normalizer_iff.1 (hG₂I e.2) _).1 (I₂.inv_mem y.2))
      · exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.1 (hG₂C (hIG₂ y.2)) _).1 heC)
          (Subgroup.inv_mem _ heC)
    have h1 : π (⟨y, hIG₂ y.2⟩ * e * (⟨y, hIG₂ y.2⟩)⁻¹ * e⁻¹) = 1 := (hπ1 _).2 hcomm
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hyb] at h1
    calc π e * yb = (yb * π e * yb⁻¹ * (π e)⁻¹)⁻¹ * (yb * π e) := by group
      _ = yb * π e := by rw [h1, inv_one, one_mul]
  have hrankQ := L1296.succ_le_pRank_of_commute Nat.prime_three hĒ hĒcard
    (fun e he => Subgroup.mem_centralizer_iff.1 hybC e he) hyb3 hybE le_top
    (Subgroup.mem_top yb)
  have hNp : ¬ 3 ∣ Nat.card ↥(N.subgroupOf G₂) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNG₂).toEquiv]
    obtain ⟨m, hm⟩ := hICp.exists_card_eq
    rw [hm]
    intro h3
    exact absurd ((Nat.Prime.dvd_of_dvd_pow Nat.prime_three) h3) (by norm_num)
  rw [CFSG.SectionRank.pRank_quotient_eq (N.subgroupOf G₂) hNp] at hrankQ
  have hG₂rank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥G₂) ≤ CFSG.Open.pRank 3 G₂ := by
    have h1 := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) G₂.subtype
      G₂.subtype_injective ⊤
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  have hloc : IsTwoLocal G₂ := by
    refine ⟨V₂, fun hb => ?_, hT2.to_le (hV₂.1.trans (hyp.le_and_normalizes h1222).1), rfl⟩
    have h1 := hV₂.2.1
    rw [hb, Subgroup.card_bot] at h1
    norm_num at h1
  have h2 := CFSG.Quasithin.pRank_le_two_of_isTwoLocal hyp.qtke hloc Nat.prime_three
    (by norm_num)
  omega

end CFSG.Quasithin.H13
