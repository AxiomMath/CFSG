module

public import CFSG.Quasithin.EmptyFaithful.S151cShapeD10
public import CFSG.Quasithin.Recognition.F112WLocal2
public import CFSG.Quasithin.EmptyFaithful.S151cTwo

public section

namespace CFSG.Quasithin

open CFSG.Open

section ShapeNineAux151c

variable {V : Type} [CommGroup V]

private theorem nine_mem_of_odd_orderOf_of_index_eq_two {G : Type*} [Group G] {Q : Subgroup G}
    (hQ : Q.index = 2) {y : G} (hy : Odd (orderOf y)) : y ∈ Q := by
  have : Q.Normal := Subgroup.normal_of_index_eq_two hQ
  have h1 : orderOf (QuotientGroup.mk y : G ⧸ Q) ∣ orderOf y :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one]; simp)
  have h2 : orderOf (QuotientGroup.mk y : G ⧸ Q) ∣ 2 := by
    have := orderOf_dvd_natCard (QuotientGroup.mk y : G ⧸ Q)
    rwa [← Subgroup.index_eq_card, hQ] at this
  have h3 : orderOf (QuotientGroup.mk y : G ⧸ Q) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · exfalso
      rw [h] at h1
      exact (Nat.not_even_iff_odd.mpr hy) (even_iff_two_dvd.mpr h1)
  exact (QuotientGroup.eq_one_iff y).mp (orderOf_eq_one_iff.mp h3)

private theorem nine_inf_centSub_commV_eq_bot [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {P : Subgroup (MulAut V)} (hP3 : Nat.card P = 3) : P ⊓ centSub (commV P) = ⊥ := by
  obtain ⟨hsup, -, -, -⟩ := commV_card_three hV hP3
  refine (Subgroup.eq_bot_iff_forall _).mpr fun p hp => ?_
  refine MulEquiv.ext fun v => ?_
  have hv : v ∈ commV P ⊔ fixV P := by rw [hsup]; exact Subgroup.mem_top v
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hv
  rw [map_mul, hp.2 a ha, hb p hp.1, MulAut.one_apply]

private theorem nine_exists_mem_of_odd_stab [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {U : Subgroup V}
    (hU : rk U = 2) {P : Subgroup (MulAut V)} (hP3 : Nat.card P = 3) (hPs : P ≤ stabSub U)
    (hker : P ⊓ centSub U = ⊥) {y : MulAut V} (hy : y ∈ stabSub U) (hodd : Odd (orderOf y)) :
    ∃ p ∈ P, ∀ u ∈ U, p u = y u := by
  have hVU : ∀ v : U, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV v)
  have h6 : Nat.card (MulAut U) = 6 := card_mulAut_of_rk_two hVU hU
  have hmul := card_autSub_mul hPs
  rw [hker, Subgroup.card_bot, mul_one, hP3] at hmul
  have hidx : (autSub P U).index = 2 := by
    have := Subgroup.card_mul_index (autSub P U)
    rw [hmul, h6] at this
    omega
  have hy' : Odd (orderOf (resHom U ⟨y, hy⟩)) := by
    have h1 : orderOf (resHom U ⟨y, hy⟩) ∣ orderOf (⟨y, hy⟩ : stabSub U) :=
      orderOf_map_dvd (resHom U) _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hodd h1
  have hmem := nine_mem_of_odd_orderOf_of_index_eq_two hidx hy'
  obtain ⟨g, hgP, hg⟩ := mem_autSub.mp hmem
  refine ⟨(g : MulAut V), hgP, fun u hu => ?_⟩
  have := congrArg (fun φ : MulAut U => ((φ ⟨u, hu⟩ : U) : V)) hg
  simpa [resHom_apply] using this

private theorem nine_nonempty_zmod_of_cyclic {G : Type*} [Group G] (hG : IsCyclic G) {n : ℕ}
    (h : Nat.card G = n) : Nonempty (G ≃* Multiplicative (ZMod n)) := by
  subst h
  exact ⟨(zmodCyclicMulEquiv hG).symm⟩

private theorem nine_nonempty_mulEquiv_zmod_four [Finite V] {T N : Subgroup (MulAut V)}
    {σ : MulAut V} (hσ : σ ∈ T) (hcard : Nat.card N ∣ 2) (hσN : σ * σ ∈ N) (hσ2 : σ * σ ≠ 1)
    (hcos : ∀ x ∈ T, x ∈ N ∨ σ⁻¹ * x ∈ N) : Nonempty (↥T ≃* Multiplicative (ZMod 4)) := by
  have h1 : orderOf (σ * σ) ∣ 2 := by
    have := orderOf_dvd_natCard (⟨σ * σ, hσN⟩ : N)
    rw [Subgroup.orderOf_mk] at this
    exact this.trans hcard
  have h2 : orderOf (σ * σ) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hσ2
    · exact h
  have hσ4 : σ ^ 4 = 1 := by
    have : (σ * σ) ^ 2 = 1 := by
      have := pow_orderOf_eq_one (σ * σ)
      rwa [h2] at this
    calc σ ^ 4 = (σ * σ) ^ 2 := by rw [← pow_two, ← pow_mul]
      _ = 1 := this
  have hord : orderOf σ = 4 := by
    have hd : orderOf σ ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hσ4)
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    interval_cases j
    · exfalso
      apply hσ2
      have : σ = 1 := orderOf_eq_one_iff.mp (by simpa using hj')
      rw [this, mul_one]
    · exfalso
      apply hσ2
      rw [← pow_two]
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hj']; norm_num)
    · simpa using hj'
  have hzN : Subgroup.zpowers (σ * σ) ≤ N := Subgroup.zpowers_le.mpr hσN
  have hNeq : N = Subgroup.zpowers (σ * σ) := by
    refine (Subgroup.eq_of_le_of_card_ge hzN ?_).symm
    rw [Nat.card_zpowers, h2]
    exact Nat.le_of_dvd (by norm_num) hcard
  have hzσ : Subgroup.zpowers (σ * σ) ≤ Subgroup.zpowers σ := by
    rw [Subgroup.zpowers_le, ← pow_two]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) 2
  have hTeq : T = Subgroup.zpowers σ := by
    apply le_antisymm
    · intro x hx
      rcases hcos x hx with hxN | hxN
      · exact hzσ (hNeq ▸ hxN)
      · have h3 : σ⁻¹ * x ∈ Subgroup.zpowers σ := hzσ (hNeq ▸ hxN)
        have := (Subgroup.zpowers σ).mul_mem (Subgroup.mem_zpowers σ) h3
        simpa using this
    · exact Subgroup.zpowers_le.mpr hσ
  have hcardT : Nat.card T = 4 := by rw [hTeq, Nat.card_zpowers, hord]
  have hcyc : IsCyclic T :=
    isCyclic_of_orderOf_eq_card (⟨σ, hσ⟩ : T) (by rw [Subgroup.orderOf_mk, hord, hcardT])
  exact nine_nonempty_zmod_of_cyclic hcyc hcardT

theorem two_le_rk_commV_of_qhat [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    {r : ℚ} (hq : qhatOf X = (r : WithTop ℚ)) (hr : r = 2) {g : MulAut V} (hgX : g ∈ X)
    (hg1 : g ≠ 1) (hg2 : ∃ k : ℕ, g ^ 2 ^ k = 1) : 2 ≤ rk (commV (Subgroup.zpowers g)) := by
  obtain ⟨k, hk⟩ := hg2
  have hord : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  have hj1 : j ≠ 0 := by
    rintro rfl
    exact hg1 (orderOf_eq_one_iff.mp (by simpa using hj))
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  set c : MulAut V := g ^ 2 ^ i with hc
  have hc2 : c ^ 2 = 1 := by
    rw [hc, ← pow_mul, ← pow_succ, ← hj]
    exact pow_orderOf_eq_one g
  have hc1 : c ≠ 1 := by
    intro h1
    have h2 : orderOf g ∣ 2 ^ i := orderOf_dvd_of_pow_eq_one h1
    rw [hj] at h2
    have h3 := Nat.le_of_dvd (by positivity) h2
    have h4 : 2 ^ i < 2 ^ (i + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hcX : c ∈ X := X.pow_mem hgX _
  have hrk1 := one_le_rk_commV_zpowers hV hc1
  have hne1 : rk (commV (Subgroup.zpowers c)) ≠ 1 := fun e =>
    not_transvection hV hq (by rw [hr]; norm_num) hcX hc1 hc2 e
  have hle : commV (Subgroup.zpowers c) ≤ commV (Subgroup.zpowers g) :=
    commV_mono216 (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers g) _))
  have := rk_mono hle
  omega

theorem le_Xc_of_invariant_fixV [Finite V] {X Tb Xc : Subgroup (MulAut V)}
    (hs : Setting151c X Tb Xc) {P : Subgroup (MulAut V)} (hPX : P ≤ X) {U : Subgroup V}
    (hUne : U ≠ ⊥) (hU : ∀ g ∈ Tb, ∀ u ∈ U, g u ∈ U) (hPU : U ≤ fixV P) : P ≤ Xc := by
  have hpos := rk_inf_fixV_pos_of_isPGroup_two hs.sq hs.syl.2.1 hU hUne
  have hne : U ⊓ fixV Tb ≠ ⊥ := (rk_pos_iff_ne_bot' hs.sq).mp hpos
  intro p hp
  exact hs.hU (U ⊓ fixV Tb) inf_le_right hne ⟨hPX hp, fun w hw => hPU hw.1 p hp⟩

structure E9Planes151c (J P₁ P₂ : Subgroup (MulAut V)) : Prop where
  mem₁ : P₁ ∈ Xk J 1
  mem₂ : P₂ ∈ Xk J 1
  disj : Disjoint (commV P₁) (commV P₂)
  sup : commV P₁ ⊔ commV P₂ = ⊤
  le₁₂ : commV P₁ ≤ fixV P₂
  le₂₁ : commV P₂ ≤ fixV P₁
  fsup : P₁ ⊔ P₂ = fittingOf J
  char : ∀ P : Subgroup (MulAut V), P ≤ fittingOf J → Nat.card P = 3 → fixV P ≠ ⊥ →
    P = P₁ ∨ P = P₂

namespace E9Planes151c

variable {J P₁ P₂ X : Subgroup (MulAut V)}

theorem symm (h : E9Planes151c J P₁ P₂) : E9Planes151c J P₂ P₁ where
  mem₁ := h.mem₂
  mem₂ := h.mem₁
  disj := h.disj.symm
  sup := by rw [sup_comm]; exact h.sup
  le₁₂ := h.le₂₁
  le₂₁ := h.le₁₂
  fsup := by rw [sup_comm]; exact h.fsup
  char := fun P hP h3 hf => (h.char P hP h3 hf).symm

theorem card₁ (h : E9Planes151c J P₁ P₂) : Nat.card P₁ = 3 := by
  have := h.mem₁.2.1
  omega

theorem card₂ (h : E9Planes151c J P₁ P₂) : Nat.card P₂ = 3 := h.symm.card₁

theorem rk₁ (h : E9Planes151c J P₁ P₂) : rk (commV P₁) = 2 := by
  have := h.mem₁.2.2
  omega

theorem rk₂ (h : E9Planes151c J P₁ P₂) : rk (commV P₂) = 2 := h.symm.rk₁

theorem commV_ne_bot₁ (h : E9Planes151c J P₁ P₂) : commV P₁ ≠ ⊥ := by
  intro hb
  have := h.rk₁
  rw [hb, rk_bot] at this
  omega

theorem commV_ne_bot₂ (h : E9Planes151c J P₁ P₂) : commV P₂ ≠ ⊥ := h.symm.commV_ne_bot₁

theorem ne (h : E9Planes151c J P₁ P₂) : P₁ ≠ P₂ := by
  intro heq
  subst heq
  exact h.commV_ne_bot₁ (disjoint_self.mp h.disj)

theorem le_fittingOf₁ (h : E9Planes151c J P₁ P₂) : P₁ ≤ fittingOf J := h.mem₁.1

theorem le_fittingOf₂ (h : E9Planes151c J P₁ P₂) : P₂ ≤ fittingOf J := h.mem₂.1

theorem conj_mem [Finite V] (h : E9Planes151c J P₁ P₂) (hn : NormalIn X J) {x : MulAut V}
    (hx : x ∈ X) {P : Subgroup (MulAut V)} (hPF : P ≤ fittingOf J) (hP3 : Nat.card P = 3)
    (hfix : fixV P ≠ ⊥) : conjBy x P = P₁ ∨ conjBy x P = P₂ := by
  have hle : conjBy x P ≤ fittingOf J := by
    rintro _ ⟨y, hy, rfl⟩
    exact conj_mem_fittingOf_of_normalIn151c hn hx (hPF hy)
  have hcard : Nat.card (conjBy x P) = 3 := by rw [card_conjBy]; exact hP3
  have hfixne : fixV (conjBy x P) ≠ ⊥ := by
    rw [fixV_conjBy]
    intro hbot
    exact hfix ((Subgroup.map_eq_bot_iff_of_injective _ (x : V ≃* V).injective).mp hbot)
  exact h.char _ hle hcard hfixne

theorem conj_cases [Finite V] (h : E9Planes151c J P₁ P₂) (hn : NormalIn X J) {x : MulAut V}
    (hx : x ∈ X) :
    (conjBy x P₁ = P₁ ∧ conjBy x P₂ = P₂) ∨ (conjBy x P₁ = P₂ ∧ conjBy x P₂ = P₁) := by
  have hf1 : fixV P₁ ≠ ⊥ := fun hb => h.commV_ne_bot₂ (le_bot_iff.mp (hb ▸ h.le₂₁))
  have hf2 : fixV P₂ ≠ ⊥ := fun hb => h.commV_ne_bot₁ (le_bot_iff.mp (hb ▸ h.le₁₂))
  have c1 := h.conj_mem hn hx h.le_fittingOf₁ h.card₁ hf1
  have c2 := h.conj_mem hn hx h.le_fittingOf₂ h.card₂ hf2
  have hd : conjBy x P₁ ≠ conjBy x P₂ := fun e => h.ne (conjBy_injective x e)
  rcases c1 with c1 | c1 <;> rcases c2 with c2 | c2
  · exact absurd (c1.trans c2.symm) hd
  · exact Or.inl ⟨c1, c2⟩
  · exact Or.inr ⟨c1, c2⟩
  · exact absurd (c1.trans c2.symm) hd

theorem odd_mem [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (h : E9Planes151c J P₁ P₂)
    (hn : NormalIn X J) {y : MulAut V} (hyX : y ∈ X) (hodd : Odd (orderOf y)) :
    y ∈ fittingOf J := by
  rcases h.conj_cases hn hyX with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hy1 : y ∈ stabSub (commV P₁) := mem_stabSub_commV_of_conjBy h1
    have hy2 : y ∈ stabSub (commV P₂) := mem_stabSub_commV_of_conjBy h2
    obtain ⟨p₁, hp₁, e₁⟩ := nine_exists_mem_of_odd_stab hV h.rk₁ h.card₁ (le_stabSub_commV P₁)
      (nine_inf_centSub_commV_eq_bot hV h.card₁) hy1 hodd
    obtain ⟨p₂, hp₂, e₂⟩ := nine_exists_mem_of_odd_stab hV h.rk₂ h.card₂ (le_stabSub_commV P₂)
      (nine_inf_centSub_commV_eq_bot hV h.card₂) hy2 hodd
    have hy : y = p₁ * p₂ := by
      refine MulEquiv.ext fun v => ?_
      have hv : v ∈ commV P₁ ⊔ commV P₂ := by rw [h.sup]; exact Subgroup.mem_top v
      obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.mp hv
      have hp₂u₂ : p₂ u₂ ∈ commV P₂ := ((le_stabSub_commV P₂) hp₂ u₂).mpr hu₂
      have h1' : p₂ u₁ = u₁ := h.le₁₂ hu₁ p₂ hp₂
      have h2' : p₁ (p₂ u₂) = p₂ u₂ := h.le₂₁ hp₂u₂ p₁ hp₁
      rw [MulAut.mul_apply, map_mul, map_mul, map_mul, h1', h2', e₁ u₁ hu₁, e₂ u₂ hu₂]
    rw [← h.fsup, hy]
    exact Subgroup.mul_mem_sup hp₁ hp₂
  · exfalso
    obtain ⟨m, hm⟩ := hodd
    have hy2 : conjBy (y * y) P₁ = P₁ := by rw [← conjBy_conjBy, h1, h2]
    have hpow : y ^ (2 * m + 2) = (y * y) ^ (m + 1) := by
      rw [← pow_two, ← pow_mul]
      ring_nf
    have hyo : y ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one y
    have hyy : y = (y * y) ^ (m + 1) := by
      rw [← hpow, pow_succ y (2 * m + 1), hyo, one_mul]
    have : conjBy y P₁ = P₁ := by
      conv_lhs => rw [hyy]
      exact conjBy_pow_eq hy2 _
    exact h.ne (this.symm.trans h1)

theorem rk_commV_swap_le [Finite V] (hrk : rk V = 4) (h : E9Planes151c J P₁ P₂) {σ : MulAut V}
    (hσ2 : σ ^ 2 = 1) (h1 : conjBy σ P₁ = P₂) : rk (commV (Subgroup.zpowers σ)) ≤ 2 := by
  let ψ : V →* V :=
    { toFun := fun v => v * σ v
      map_one' := by simp
      map_mul' := by intro a b; rw [map_mul]; exact mul_mul_mul_comm _ _ _ _ }
  have hψapp : ∀ v, ψ v = v * σ v := fun v => rfl
  have hσσ : ∀ v, σ (σ v) = v := by
    intro v
    have : (σ * σ) v = v := by rw [← pow_two, hσ2, MulAut.one_apply]
    exact this
  have hker : commV P₁ ⊓ ψ.ker = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun v hv => ?_
    obtain ⟨hv1, hv2⟩ := hv
    have hψ : v * σ v = 1 := by rw [← hψapp]; exact MonoidHom.mem_ker.mp hv2
    have hσv : σ v ∈ commV P₂ := commV_apply_of_conjBy h1 hv1
    have hσv' : σ v ∈ commV P₁ := by
      have : σ v = v⁻¹ := eq_inv_of_mul_eq_one_right hψ
      rw [this]
      exact (commV P₁).inv_mem hv1
    have hmem : σ v ∈ commV P₁ ⊓ commV P₂ := ⟨hσv', hσv⟩
    rw [disjoint_iff.mp h.disj, Subgroup.mem_bot] at hmem
    have := congrArg σ hmem
    rw [hσσ, map_one] at this
    exact this
  have hr := rk_map_add_rk_inf_ker ψ (commV P₁)
  rw [hker, rk_bot, add_zero, h.rk₁] at hr
  have hle : (commV P₁).map ψ ≤ fixV (Subgroup.zpowers σ) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [mem_fixV_zpowers_iff, hψapp, map_mul, hσσ, mul_comm]
  have h2 := rk_mono hle
  have h3 := rk_commV_add_rk_fixV σ
  omega

theorem card_dvd_two_of_stab [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hrk : rk V = 4)
    (h : E9Planes151c J P₁ P₂) {N : Subgroup (MulAut V)} (hN : IsPGroup 2 N)
    (hNs : ∀ n ∈ N, conjBy n P₁ = P₁ ∧ conjBy n P₂ = P₂)
    (h2 : ∀ g ∈ N, g ≠ 1 → 2 ≤ rk (commV (Subgroup.zpowers g))) : Nat.card N ∣ 2 := by
  have hNst : N ≤ stabSub (commV P₁) := fun n hn => mem_stabSub_commV_of_conjBy (hNs n hn).1
  let ρ : ↥N →* MulAut ↥(commV P₁) := (resHom (commV P₁)).comp (Subgroup.inclusion hNst)
  have hρ : ∀ (m : N) (u : V) (hu : u ∈ commV P₁),
      ((ρ m ⟨u, hu⟩ : ↥(commV P₁)) : V) = (m : MulAut V) u := by
    intro m u hu
    simp [ρ, resHom_apply]
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro n hn
    by_contra hn1
    have hn1' : (n : MulAut V) ≠ 1 := fun e => hn1 (Subtype.ext e)
    have hfix1 : ∀ u ∈ commV P₁, (n : MulAut V) u = u := by
      intro u hu
      have := hρ n u hu
      rw [hn] at this
      simpa using this.symm
    have hzN : Subgroup.zpowers (n : MulAut V) ≤ N := Subgroup.zpowers_le.mpr n.2
    have hz2 : IsPGroup 2 (Subgroup.zpowers (n : MulAut V)) := hN.to_le hzN
    have hinv : ∀ g ∈ Subgroup.zpowers (n : MulAut V), ∀ u ∈ commV P₂, g u ∈ commV P₂ :=
      fun g hg u hu => commV_apply_of_conjBy (hNs g (hzN hg)).2 hu
    have hpos := rk_inf_fixV_pos_of_isPGroup_two hV hz2 hinv h.commV_ne_bot₂
    set W : Subgroup V := commV P₂ ⊓ fixV (Subgroup.zpowers (n : MulAut V))
    have hU1 : commV P₁ ≤ fixV (Subgroup.zpowers (n : MulAut V)) := fun u hu =>
      mem_fixV_zpowers_iff.mpr (hfix1 u hu)
    have hsupfix : commV P₁ ⊔ W ≤ fixV (Subgroup.zpowers (n : MulAut V)) :=
      sup_le hU1 inf_le_right
    have hinf : commV P₁ ⊓ W = ⊥ := by
      refine eq_bot_iff.mpr ?_
      rw [← disjoint_iff.mp h.disj]
      exact inf_le_inf_left _ inf_le_left
    have hrksum := rk_sup_add_rk_inf (commV P₁) W
    rw [hinf, rk_bot, h.rk₁] at hrksum
    have h3 := rk_mono hsupfix
    have h4 := rk_commV_add_rk_fixV (n : MulAut V)
    have h5 := h2 (n : MulAut V) n.2 hn1'
    omega
  have hdvd := Subgroup.card_dvd_of_injective ρ hinj
  have hVU : ∀ v : ↥(commV P₁), v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV v)
  rw [card_mulAut_of_rk_two hVU h.rk₁] at hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hN
  rw [hk] at hdvd ⊢
  exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3))
    (by simpa using hdvd : 2 ^ k ∣ 2 * 3)

theorem exists_swap [Finite V] {Tb Xc : Subgroup (MulAut V)} (h : E9Planes151c J P₁ P₂)
    (hn : NormalIn X J) (hJX : J ≤ X) (hs : Setting151c X Tb Xc) (hXT : Tb ⊔ fittingOf J = X) :
    ∃ σ ∈ Tb, conjBy σ P₁ = P₂ := by
  by_contra hcon
  push Not at hcon
  have hfix : ∀ σ ∈ Tb, conjBy σ P₁ = P₁ ∧ conjBy σ P₂ = P₂ := by
    intro σ hσ
    rcases h.conj_cases hn (hs.syl.1 hσ) with h1 | h1
    · exact h1
    · exact absurd h1.1 (hcon σ hσ)
  have hP1 : P₁ ≤ Xc := le_Xc_of_invariant_fixV hs
    ((h.le_fittingOf₁.trans (fittingOf_le J)).trans hJX) h.commV_ne_bot₂
    (fun g hg u hu => commV_apply_of_conjBy (hfix g hg).2 hu) h.le₂₁
  have hP2 : P₂ ≤ Xc := le_Xc_of_invariant_fixV hs
    ((h.le_fittingOf₂.trans (fittingOf_le J)).trans hJX) h.commV_ne_bot₁
    (fun g hg u hu => commV_apply_of_conjBy (hfix g hg).1 hu) h.le₁₂
  apply hs.xc_ne
  rw [← hXT]
  refine sup_le hs.tb_le ?_
  rw [← h.fsup]
  exact sup_le hP1 hP2

theorem le_normalizer (h : E9Planes151c J P₁ P₂) (hE : IsElemAbelian 3 (fittingOf J))
    {t : MulAut V} (ht2 : t ^ 2 = 1) (hinv : ∀ f ∈ fittingOf J, t * f * t⁻¹ = f⁻¹)
    (hJ : J = fittingOf J ⊔ Subgroup.zpowers t) :
    J ≤ Subgroup.normalizer (P₁ : Set (MulAut V)) := by
  have hab : IsMulCommutative ↥(fittingOf J) := hE.1
  have hF : fittingOf J ≤ Subgroup.normalizer (P₁ : Set (MulAut V)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le_fittingOf₁).mp inferInstance
  have ht' : t ∈ Subgroup.normalizer (P₁ : Set (MulAut V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hinv x (h.le_fittingOf₁ hx)]
      exact P₁.inv_mem hx
    · intro hx
      have hq : t * (t * x * t⁻¹) * t⁻¹ = (t * x * t⁻¹)⁻¹ := hinv _ (h.le_fittingOf₁ hx)
      have e : t * (t * x * t⁻¹) * t⁻¹ = x := by
        have h1 : t * t = 1 := by rw [← pow_two]; exact ht2
        have h1' : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, h1, inv_one]
        calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
          _ = x := by rw [h1, h1', one_mul, mul_one]
      rw [e] at hq
      rw [hq]
      exact P₁.inv_mem hx
  rw [hJ]
  exact sup_le hF (Subgroup.zpowers_le.mpr ht')

end E9Planes151c

end ShapeNineAux151c

section ShapeNine151c

variable {V : Type} [CommGroup V] [Finite V] {X Tb Xc J : Subgroup (MulAut V)} {r : ℚ}

theorem shape_Nine (B : OneBlock151c X Tb Xc J r) (hE : IsElemAbelian 3 (fittingOf J))
    (hF9 : Nat.card (fittingOf J) = 9)
    (ht : ∃ t ∈ J, orderOf t = 2 ∧ (∀ f ∈ fittingOf J, t * f * t⁻¹ = f⁻¹) ∧
      J = fittingOf J ⊔ Subgroup.zpowers t) (hr : r = 2) (hrk : rk V = 4) : ACase4 X Tb J := by
  have hcard : Nat.card V = 16 := by
    rw [card_eq_two_pow_rk B.sq, hrk]
    norm_num
  obtain ⟨P₁, P₂, h1, h2, hdisj, hsup, hle12, hle21, hFsup, hchar⟩ :=
    exists_planes_E9 B.sq hE hF9 B.hyp.comm_fitting hrk
  have hpl : E9Planes151c J P₁ P₂ := ⟨h1, h2, hdisj, hsup, hle12, hle21, hFsup, hchar⟩
  have hO : oTwoUpper X = fittingOf J := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨hyX, hyo⟩
      exact hpl.odd_mem B.sq B.normal hyX hyo
    · intro f hf
      refine mem_oTwoUpper_of_odd ((fittingOf_le J).trans B.le hf) ?_
      exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one (hE.2 f hf))
  have hXT : Tb ⊔ fittingOf J = X := by
    have := F112W.sup_oTwoUpper_eq_of_isSylowTwoOf
      (B.syl : CFSG.QuasithinUnique.IsSylowTwoOf Tb X)
    rwa [hO] at this
  obtain ⟨σ, hσT, hσ⟩ := hpl.exists_swap B.normal B.le B.setting hXT
  have hσ' : conjBy σ P₂ = P₁ := by
    rcases hpl.conj_cases B.normal (B.tb_le hσT) with h | h
    · exact absurd (h.1.symm.trans hσ) hpl.ne
    · exact h.2
  obtain ⟨t, -, ht2, htinv, hJt⟩ := ht
  have ht2' : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2] at this
  have hJN := hpl.le_normalizer hE ht2' htinv hJt
  have hσ2 : σ * σ ≠ 1 := by
    intro hσσ
    have hσ2' : σ ^ 2 = 1 := by rw [pow_two]; exact hσσ
    have hσ1 : σ ≠ 1 := by
      rintro rfl
      rw [conjBy_one] at hσ
      exact hpl.ne hσ
    have hrk2 := hpl.rk_commV_swap_le hrk hσ2' hσ
    have hσJ : σ ∈ J := B.offender (B.tb_le hσT) hσ1 hσ2' (by rw [hr]; exact_mod_cast hrk2)
    exact hpl.ne ((conjBy_eq_of_mem_normalizer (hJN hσJ)).symm.trans hσ)
  have hTb2 : IsPGroup 2 Tb := B.syl.2.1
  have hN2 : IsPGroup 2 (stabConj Tb P₁) := hTb2.to_le fun x hx => hx.1
  have hNs : ∀ n ∈ stabConj Tb P₁, conjBy n P₁ = P₁ ∧ conjBy n P₂ = P₂ := by
    intro n hn
    rcases hpl.conj_cases B.normal (B.tb_le hn.1) with h | h
    · exact h
    · exact absurd (h.1.symm.trans hn.2) hpl.ne.symm
  have hcard2 : Nat.card (stabConj Tb P₁) ∣ 2 := by
    refine hpl.card_dvd_two_of_stab B.sq hrk hN2 hNs fun g hg hg1 => ?_
    refine two_le_rk_commV_of_qhat B.sq B.qhat hr (B.tb_le hg.1) hg1 ?_
    obtain ⟨k, hk⟩ := hTb2 ⟨g, hg.1⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hσN : σ * σ ∈ stabConj Tb P₁ :=
    ⟨Tb.mul_mem hσT hσT, by rw [← conjBy_conjBy, hσ, hσ']⟩
  have hcos : ∀ x ∈ Tb, x ∈ stabConj Tb P₁ ∨ σ⁻¹ * x ∈ stabConj Tb P₁ := by
    intro x hx
    rcases hpl.conj_cases B.normal (B.tb_le hx) with h | h
    · exact Or.inl ⟨hx, h.1⟩
    · refine Or.inr ⟨Tb.mul_mem (Tb.inv_mem hσT) hx, ?_⟩
      rw [← conjBy_conjBy, h.1, conjBy_inv_eq_of_eq hσ]
  have hT4 := nine_nonempty_mulEquiv_zmod_four hσT hcard2 hσN hσ2 hcos
  refine ⟨hcard, ?_, hT4⟩
  unfold AElementaryNine
  rw [hO]
  exact ⟨hE, hF9, t, ht2, htinv, hJt⟩

end ShapeNine151c

end CFSG.Quasithin
