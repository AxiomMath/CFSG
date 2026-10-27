module

public import CFSG.Quasithin.SteinbergBSConjugateOrbits

public section

namespace CFSG.Quasithin.SteinbergBS

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def commIn (N : Subgroup G) [N.Normal] (X : Set G) : Subgroup G where
  carrier := {g | ∀ x ∈ X, ⁅x, g⁆ ∈ N}
  one_mem' := fun x _ => by
    rw [commutatorElement_one_right]
    exact N.one_mem
  mul_mem' := fun {g h} hg hh x hx => by
    have e : ⁅x, g * h⁆ = ⁅x, g⁆ * (g * ⁅x, h⁆ * g⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact N.mul_mem (hg x hx) (‹N.Normal›.conj_mem _ (hh x hx) g)
  inv_mem' := fun {g} hg x hx => by
    have e : ⁅x, g⁻¹⁆ = g⁻¹ * ⁅x, g⁆⁻¹ * g⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact ‹N.Normal›.conj_mem _ (N.inv_mem (hg x hx)) g⁻¹

theorem mem_commIn {N : Subgroup G} [N.Normal] {X : Set G} {g : G} :
    g ∈ commIn N X ↔ ∀ x ∈ X, ⁅x, g⁆ ∈ N :=
  Iff.rfl

theorem commIn_normal (N X : Subgroup G) [N.Normal] [hX : X.Normal] :
    (commIn N (X : Set G)).Normal :=
  ⟨fun y hy g x hx => by
    have hx' : g⁻¹ * x * g ∈ X := by
      have h1 := hX.conj_mem x hx g⁻¹
      rwa [inv_inv] at h1
    have e : ⁅x, g * y * g⁻¹⁆ = g * ⁅g⁻¹ * x * g, y⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact ‹N.Normal›.conj_mem _ (hy _ hx') g⟩

theorem le_normalizer_of_forall_conj_mem {S P : Subgroup G}
    (h : ∀ s ∈ S, ∀ p ∈ P, s * p * s⁻¹ ∈ P) : S ≤ normalizer (P : Set G) := by
  intro s hs
  rw [mem_normalizer_iff]
  intro p
  refine ⟨h s hs p, fun hp => ?_⟩
  have h1 := h s⁻¹ (inv_mem hs) _ hp
  simpa [mul_assoc] using h1

theorem commute_of_odd_orderOf {y : G} (hy : Odd (orderOf y)) {X P : Subgroup G}
    (hX : IsPGroup 2 X) (hPX : P ≤ X) (hyP : ∀ p ∈ P, y * p = p * y)
    (hyX : ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ P) : ∀ x ∈ X, y * x = x * y := by
  intro x hx
  have hcP := hyX x hx
  set c := y * x * y⁻¹ * x⁻¹ with hc
  have hyc : y * c * y⁻¹ = c := by
    rw [hyP c hcP, mul_inv_cancel_right]
  have h1 : y * x * y⁻¹ = c * x := by
    rw [hc]
    group
  have hpow : ∀ n : ℕ, y ^ n * x * (y ^ n)⁻¹ = c ^ n * x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h2 : y * c ^ n * y⁻¹ = c ^ n := by rw [← conj_pow, hyc]
      calc y ^ (n + 1) * x * (y ^ (n + 1))⁻¹ = y * (y ^ n * x * (y ^ n)⁻¹) * y⁻¹ := by group
        _ = y * (c ^ n * x) * y⁻¹ := by rw [ih]
        _ = (y * c ^ n * y⁻¹) * (y * x * y⁻¹) := by group
        _ = c ^ n * (c * x) := by rw [h1, h2]
        _ = c ^ (n + 1) * x := by group
  have hm := hpow (orderOf y)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hm
  have hcm : c ^ orderOf y = 1 := by
    have h2 : 1 * x = c ^ orderOf y * x := by rw [one_mul]; exact hm
    exact (mul_right_cancel h2).symm
  obtain ⟨r, hr⟩ := hX ⟨c, hPX hcP⟩
  have hr' : c ^ 2 ^ r = 1 := congrArg Subtype.val hr
  have hcop : Nat.Coprime (orderOf y) (2 ^ r) :=
    Nat.Coprime.pow_right r (Nat.coprime_comm.1 (Nat.coprime_two_left.2 hy))
  have hc1 : c = 1 := orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hcm) (orderOf_dvd_of_pow_eq_one hr'))
  calc y * x = c * (x * y) := by rw [hc]; group
    _ = x * y := by rw [hc1, one_mul]

theorem isPGroup_two_of_odd_mem [Finite G] {Y J : Subgroup G} (hJ : IsPGroup 2 J)
    (h : ∀ y ∈ Y, Odd (orderOf y) → y ∈ J) : IsPGroup 2 Y := by
  intro y
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (y : G)).ne'
  have hdvd : 2 ^ a ∣ orderOf (y : G) := ⟨m, hn⟩
  have hord : orderOf ((y : G) ^ 2 ^ a) = m := by
    rw [orderOf_pow_of_dvd (by positivity) hdvd, hn, Nat.mul_div_cancel_left _ (by positivity)]
  have hyJ := h _ (pow_mem y.2 _) (by rw [hord]; exact hm)
  obtain ⟨r, hr⟩ := hJ ⟨_, hyJ⟩
  have hr' : ((y : G) ^ 2 ^ a) ^ 2 ^ r = 1 := congrArg Subtype.val hr
  have h1 : m ∣ 2 ^ r := hord ▸ orderOf_dvd_of_pow_eq_one hr'
  have hm1 : m = 1 := Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_right r (Nat.coprime_comm.1 (Nat.coprime_two_left.2 hm))) dvd_rfl h1
  refine ⟨a, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  rw [hm1] at hord
  exact orderOf_eq_one_iff.1 hord

theorem qrc_conjugate_pair_produces_cubic_action_and_exact_kernel {I : Type*} [Group I]
    [Finite I] (hchar : IsCharacteristicP 2 I) (T : Sylow 2 I) {V : Subgroup I}
    [IsElementaryAbelian 2 V] (hVT : V ≤ T) (hTV : (T : Subgroup I) ≤ normalizer (V : Set I))
    {g : I} (hI : V ⊔ conjugate V g = ⊤) (hVI : V < ⊤) {M J B A P Z : Subgroup I}
    (hJdef : J = ⨅ i : I, conjugate M i) (hJ : (⨅ i : I, conjugate M i) = pCore 2 I)
    (hBdef : B = V ⊓ J) (hAdef : A = conjugate V g ⊓ J) (hPdef : P = B ⊔ A)
    (hZdef : Z = V ⊓ conjugate V g) :
    A = conjugate B g ∧ P.Normal ∧ Z ≤ center I ∧
    (Z ≤ B ∧ Z ≤ A ∧ B ⊓ A = Z ∧ (∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ Z) ∧ ∀ x ∈ P, x * x ∈ Z) ∧
    Z.relIndex A = Z.relIndex B ∧ ⁅⁅⁅V, A⁆, A⁆, A⁆ = ⊥ ∧ ⁅V, A⁆ ≠ ⊥ ∧
    A ⊓ centralizer (V : Set I) = Z ∧ ⁅J, ⊤⁆ ≤ P ∧
    (∀ y : I, (∀ x ∈ P, y * x * y⁻¹ * x⁻¹ ∈ Z) → y ∈ J) ∧
    Nat.log 2 ((V ⊓ centralizer (A : Set I)).relIndex V) ≤
      Nat.log 2 (Z.relIndex A) + Nat.log 2 (B.relIndex V) := by
  classical
  have hJ' : J = pCore 2 I := hJdef.trans hJ
  have hJn : J.Normal := by rw [hJ']; infer_instance
  have hJp : IsPGroup 2 J := by rw [hJ']; exact pCore_isPGroup
  have hJT : J ≤ T := hJp.le_sylow_of_normal T
  have hJV : J ≤ normalizer (V : Set I) := hJT.trans hTV
  have hJC : centralizer (J : Set I) ≤ J := by rw [hJ']; exact hchar
  have hVp : IsPGroup 2 V := T.isPGroup'.to_le hVT
  have hV2 : ∀ v ∈ V, v * v = 1 := fun v hv => by
    rw [← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian v hv
  have hVab : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val (mul_comm' (⟨v, hv⟩ : V) ⟨w, hw⟩)
  have hWab : ∀ w ∈ conjugate V g, ∀ w' ∈ conjugate V g, w * w' = w' * w := by
    intro w hw w' hw'
    have h1 := hVab _ (mem_conjugate_iff.1 hw) _ (mem_conjugate_iff.1 hw')
    calc w * w' = g⁻¹ * ((g * w * g⁻¹) * (g * w' * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * w' * g⁻¹) * (g * w * g⁻¹)) * g := by rw [h1]
      _ = w' * w := by group
  have hW2 : ∀ w ∈ conjugate V g, w * w = 1 := by
    intro w hw
    have h1 := hV2 _ (mem_conjugate_iff.1 hw)
    calc w * w = g⁻¹ * ((g * w * g⁻¹) * (g * w * g⁻¹)) * g := by group
      _ = 1 := by rw [h1]; group
  have hJW : J ≤ normalizer (conjugate V g : Set I) := by
    refine le_normalizer_of_forall_conj_mem fun j hj x hx => ?_
    rw [mem_conjugate_iff] at hx ⊢
    have hgj : g * j * g⁻¹ ∈ J := hJn.conj_mem j hj g
    have h1 := (mem_normalizer_iff.mp (hJV hgj) (g * x * g⁻¹)).mp hx
    rw [show g * (j * x * j⁻¹) * g⁻¹ = g * j * g⁻¹ * (g * x * g⁻¹) * (g * j * g⁻¹)⁻¹ by group]
    exact h1
  have hZcen : Z ≤ center I := by
    intro z hz
    rw [hZdef] at hz
    obtain ⟨hzV, hzW⟩ := mem_inf.1 hz
    have hle : V ⊔ conjugate V g ≤ centralizer ({z} : Set I) := by
      refine sup_le (fun v hv => ?_) (fun w hw => ?_)
      · rw [mem_centralizer_singleton_iff]
        exact hVab v hv z hzV
      · rw [mem_centralizer_singleton_iff]
        exact hWab w hw z hzW
    rw [hI] at hle
    rw [mem_center_iff]
    intro h
    exact (mem_centralizer_singleton_iff.1 (hle (mem_top h)))
  have hZJ : Z ≤ J := fun z hz =>
    hJC (mem_centralizer_iff.2 fun h _ => mem_center_iff.1 (hZcen hz) h)
  have hZn : Z.Normal := ⟨fun z hz h => by
    rw [mem_center_iff.1 (hZcen hz) h, mul_inv_cancel_right]
    exact hz⟩
  have hZV : Z ≤ V := hZdef ▸ inf_le_left
  have hZW : Z ≤ conjugate V g := hZdef ▸ inf_le_right
  have hBV : B ≤ V := hBdef ▸ inf_le_left
  have hBJ : B ≤ J := hBdef ▸ inf_le_right
  have hAW : A ≤ conjugate V g := hAdef ▸ inf_le_left
  have hAJ : A ≤ J := hAdef ▸ inf_le_right
  have hZB : Z ≤ B := by rw [hBdef]; exact le_inf hZV hZJ
  have hZA : Z ≤ A := by rw [hAdef]; exact le_inf hZW hZJ
  have hBP : B ≤ P := hPdef ▸ le_sup_left
  have hAP : A ≤ P := hPdef ▸ le_sup_right
  have hPJ : P ≤ J := by rw [hPdef]; exact sup_le hBJ hAJ
  have hVJB : ∀ v ∈ V, ∀ j ∈ J, ⁅v, j⁆ ∈ B := by
    intro v hv j hj
    rw [hBdef, commutatorElement_def]
    refine mem_inf.2 ⟨?_, mul_mem (hJn.conj_mem j hj v) (inv_mem hj)⟩
    have h1 : j * v⁻¹ * j⁻¹ ∈ V := (mem_normalizer_iff.mp (hJV hj) v⁻¹).mp (inv_mem hv)
    rw [show v * j * v⁻¹ * j⁻¹ = v * (j * v⁻¹ * j⁻¹) by group]
    exact mul_mem hv h1
  have hWJA : ∀ w ∈ conjugate V g, ∀ j ∈ J, ⁅w, j⁆ ∈ A := by
    intro w hw j hj
    rw [hAdef, commutatorElement_def]
    refine mem_inf.2 ⟨?_, mul_mem (hJn.conj_mem j hj w) (inv_mem hj)⟩
    have h1 : j * w⁻¹ * j⁻¹ ∈ conjugate V g :=
      (mem_normalizer_iff.mp (hJW hj) w⁻¹).mp (inv_mem hw)
    rw [show w * j * w⁻¹ * j⁻¹ = w * (j * w⁻¹ * j⁻¹) by group]
    exact mul_mem hw h1
  have hBconj : ∀ j ∈ J, ∀ b ∈ B, j * b * j⁻¹ ∈ B := by
    intro j hj b hb
    rw [hBdef] at hb ⊢
    obtain ⟨hbV, hbJ⟩ := mem_inf.1 hb
    exact mem_inf.2 ⟨(mem_normalizer_iff.mp (hJV hj) b).mp hbV,
      mul_mem (mul_mem hj hbJ) (inv_mem hj)⟩
  have hAconj : ∀ j ∈ J, ∀ a ∈ A, j * a * j⁻¹ ∈ A := by
    intro j hj a ha
    rw [hAdef] at ha ⊢
    obtain ⟨haW, haJ⟩ := mem_inf.1 ha
    exact mem_inf.2 ⟨(mem_normalizer_iff.mp (hJW hj) a).mp haW,
      mul_mem (mul_mem hj haJ) (inv_mem hj)⟩
  have hAB : A = conjugate B g := by
    ext x
    rw [hAdef, hBdef, mem_inf, mem_conjugate_iff, mem_conjugate_iff, mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hJn.conj_mem x h2 g⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have h3 := hJn.conj_mem _ h2 g⁻¹
      simpa [mul_assoc] using h3
  have hPn : P.Normal := by
    have hcV : ∀ v ∈ V, ∀ p ∈ P, v * p * v⁻¹ ∈ P := by
      intro v hv p hp
      have h1 := hVJB v hv p (hPJ hp)
      rw [commutatorElement_def] at h1
      rw [show v * p * v⁻¹ = (v * p * v⁻¹ * p⁻¹) * p by group]
      exact mul_mem (hBP h1) hp
    have hcW : ∀ w ∈ conjugate V g, ∀ p ∈ P, w * p * w⁻¹ ∈ P := by
      intro w hw p hp
      have h1 := hWJA w hw p (hPJ hp)
      rw [commutatorElement_def] at h1
      rw [show w * p * w⁻¹ = (w * p * w⁻¹ * p⁻¹) * p by group]
      exact mul_mem (hAP h1) hp
    have hle : V ⊔ conjugate V g ≤ normalizer (P : Set I) :=
      sup_le (le_normalizer_of_forall_conj_mem hcV) (le_normalizer_of_forall_conj_mem hcW)
    rw [hI] at hle
    exact normalizer_eq_top_iff.1 (eq_top_iff.2 hle)
  have hBA : B ⊓ A = Z := by
    refine le_antisymm (fun x hx => ?_) (le_inf hZB hZA)
    obtain ⟨hxB, hxA⟩ := mem_inf.1 hx
    rw [hZdef]
    exact mem_inf.2 ⟨hBV hxB, hAW hxA⟩
  have hcommBA : ∀ b ∈ B, ∀ a ∈ A, ⁅b, a⁆ ∈ Z := by
    intro b hb a ha
    rw [← hBA, commutatorElement_def]
    refine mem_inf.2 ⟨?_, mul_mem (hAconj b (hBJ hb) a ha) (inv_mem ha)⟩
    rw [show b * a * b⁻¹ * a⁻¹ = b * (a * b⁻¹ * a⁻¹) by group]
    exact mul_mem hb (hBconj a (hAJ ha) _ (inv_mem hb))
  have hPcomm : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ Z := by
    have hsP : ∀ s ∈ (B : Set I) ∪ A, ∀ p ∈ P, ⁅s, p⁆ ∈ Z := by
      intro s hs
      have hle : P ≤ commIn Z {s} := by
        rw [hPdef]
        refine sup_le (fun b hb x hx => ?_) (fun a ha x hx => ?_)
        · rw [Set.mem_singleton_iff.1 hx]
          rcases hs with hs | hs
          · rw [commutatorElement_eq_one_iff_mul_comm.2 (hVab s (hBV hs) b (hBV hb))]
            exact one_mem Z
          · rw [← commutatorElement_inv]
            exact inv_mem (hcommBA b hb s hs)
        · rw [Set.mem_singleton_iff.1 hx]
          rcases hs with hs | hs
          · exact hcommBA s hs a ha
          · rw [commutatorElement_eq_one_iff_mul_comm.2 (hWab s (hAW hs) a (hAW ha))]
            exact one_mem Z
      exact fun p hp => hle hp s rfl
    intro x hx
    have hle : P ≤ commIn Z {x} := by
      rw [hPdef]
      refine sup_le (fun b hb y hy => ?_) (fun a ha y hy => ?_)
      · rw [Set.mem_singleton_iff.1 hy, ← commutatorElement_inv]
        exact inv_mem (hsP b (Or.inl hb) x hx)
      · rw [Set.mem_singleton_iff.1 hy, ← commutatorElement_inv]
        exact inv_mem (hsP a (Or.inr ha) x hx)
    exact fun y hy => hle hy x rfl
  have hPsq : ∀ x ∈ P, x * x ∈ Z := by
    let S : Subgroup I :=
      { carrier := {x | x ∈ P ∧ x * x ∈ Z}
        one_mem' := ⟨one_mem P, by rw [mul_one]; exact one_mem Z⟩
        mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
          have hc := hPcomm y hy.1 x hx.1
          have hcz := mem_center_iff.1 (hZcen hc)
          have hyx : y * x = ⁅y, x⁆ * x * y := by
            rw [commutatorElement_def]
            group
          have e : x * y * (x * y) = ⁅y, x⁆ * (x * x) * (y * y) := by
            calc x * y * (x * y) = x * (y * x) * y := by group
              _ = x * (⁅y, x⁆ * x * y) * y := by rw [hyx]
              _ = (x * ⁅y, x⁆) * x * (y * y) := by group
              _ = ⁅y, x⁆ * (x * x) * (y * y) := by rw [hcz x]; group
          rw [e]
          exact mul_mem (mul_mem hc hx.2) hy.2⟩
        inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by rw [← mul_inv_rev]; exact inv_mem hx.2⟩ }
    have hle : P ≤ S := by
      intro x hx
      have hle' : B ⊔ A ≤ S := sup_le
        (fun b hb => ⟨hBP hb, by rw [hV2 b (hBV hb)]; exact one_mem Z⟩)
        (fun a ha => ⟨hAP ha, by rw [hW2 a (hAW ha)]; exact one_mem Z⟩)
      rw [hPdef] at hx
      exact hle' hx
    exact fun x hx => (hle hx).2
  have hrel : Z.relIndex A = Z.relIndex B := by
    have hZg : conjugate Z g = Z := conjugate_of_mem_normalizer (by
      rw [normalizer_eq_top_iff.2 hZn]
      exact mem_top g)
    rw [hAB]
    conv_lhs => rw [← hZg]
    exact relIndex_map_map_of_injective Z B (MulAut.conj g⁻¹).injective
  have hVAP : ⁅V, A⁆ ≤ P := by
    rw [commutator_le]
    intro v hv a ha
    exact hBP (hVJB v hv a (hAJ ha))
  have hcubic : ⁅⁅⁅V, A⁆, A⁆, A⁆ = ⊥ := by
    have h2 : ⁅⁅V, A⁆, A⁆ ≤ Z := by
      rw [commutator_le]
      intro x hx a ha
      exact hPcomm x (hVAP hx) a (hAP ha)
    rw [eq_bot_iff, commutator_le]
    intro x hx a _
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (mem_center_iff.1 (hZcen (h2 hx)) a).symm
  have hX : ∀ x ∈ A, (∀ v ∈ V, ⁅v, x⁆ ∈ Z) → x ∈ Z := by
    have hZC : Z ≤ commIn Z (V : Set I) := fun z hz v _ => by
      rw [commutatorElement_eq_one_iff_mul_comm.2 (mem_center_iff.1 (hZcen hz) v)]
      exact one_mem Z
    have hXn : (A ⊓ commIn Z (V : Set I)).Normal := by
      have hcV : ∀ v ∈ V, ∀ x ∈ A ⊓ commIn Z (V : Set I), v * x * v⁻¹ ∈
          A ⊓ commIn Z (V : Set I) := by
        intro v hv x hx
        obtain ⟨hxA, hxC⟩ := mem_inf.1 hx
        have hc : ⁅v, x⁆ ∈ Z := hxC v hv
        rw [show v * x * v⁻¹ = ⁅v, x⁆ * x by rw [commutatorElement_def]; group]
        exact mem_inf.2 ⟨mul_mem (hZA hc) hxA, mul_mem (hZC hc) hxC⟩
      have hcW : ∀ w ∈ conjugate V g, ∀ x ∈ A ⊓ commIn Z (V : Set I), w * x * w⁻¹ ∈
          A ⊓ commIn Z (V : Set I) := by
        intro w hw x hx
        rw [hWab w hw x (hAW (mem_inf.1 hx).1), mul_inv_cancel_right]
        exact hx
      have hle : V ⊔ conjugate V g ≤ normalizer ((A ⊓ commIn Z (V : Set I) : Subgroup I) :
          Set I) :=
        sup_le (le_normalizer_of_forall_conj_mem hcV) (le_normalizer_of_forall_conj_mem hcW)
      rw [hI] at hle
      exact normalizer_eq_top_iff.1 (eq_top_iff.2 hle)
    intro x hxA hxV
    have h1 : g⁻¹ * x * g⁻¹⁻¹ ∈ A ⊓ commIn Z (V : Set I) :=
      hXn.conj_mem x (mem_inf.2 ⟨hxA, hxV⟩) g⁻¹
    have h2 := mem_conjugate_iff.1 (hAW (mem_inf.1 h1).1)
    have hxV' : x ∈ V := by simpa [mul_assoc] using h2
    rw [hZdef]
    exact mem_inf.2 ⟨hxV', hAW hxA⟩
  have hCAV : A ⊓ centralizer (V : Set I) = Z := by
    refine le_antisymm (fun x hx => ?_) (fun z hz => ?_)
    · obtain ⟨hxA, hxC⟩ := mem_inf.1 hx
      refine hX x hxA fun v hv => ?_
      rw [commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_iff.1 hxC v hv)]
      exact one_mem Z
    · exact mem_inf.2 ⟨hZA hz, mem_centralizer_iff.2 fun v _ => mem_center_iff.1 (hZcen hz) v⟩
  have hJIP : ⁅J, ⊤⁆ ≤ P := by
    have hle : V ⊔ conjugate V g ≤ commIn P (J : Set I) := by
      refine sup_le (fun v hv j hj => ?_) (fun w hw j hj => ?_)
      · rw [← commutatorElement_inv]
        exact inv_mem (hBP (hVJB v hv j hj))
      · rw [← commutatorElement_inv]
        exact inv_mem (hAP (hWJA w hw j hj))
    rw [hI] at hle
    rw [commutator_le]
    intro j hj i _
    exact hle (mem_top i) j hj
  have hCPZ : ∀ y : I, (∀ x ∈ P, y * x * y⁻¹ * x⁻¹ ∈ Z) → y ∈ J := by
    have hYn : (commIn Z (P : Set I)).Normal := commIn_normal Z P
    have hYp : IsPGroup 2 (commIn Z (P : Set I)) := by
      refine isPGroup_two_of_odd_mem hJp fun y hy hodd => ?_
      have hyZ : ∀ z ∈ Z, y * z = z * y := fun z hz => mem_center_iff.1 (hZcen hz) y
      have hyP := commute_of_odd_orderOf hodd (hJp.to_le hPJ) (hZB.trans hBP) hyZ
        fun x hx => by
          have h1 := inv_mem (hy x hx)
          rw [commutatorElement_inv] at h1
          exact h1
      have hyJ := commute_of_odd_orderOf hodd hJp hPJ hyP fun x hx => by
        have h1 := inv_mem (hJIP (commutator_mem_commutator hx (mem_top y)))
        rw [commutatorElement_inv] at h1
        exact h1
      exact hJC (mem_centralizer_iff.2 fun h hh => (hyJ h hh).symm)
    have hYJ : commIn Z (P : Set I) ≤ J := by
      rw [hJ']
      exact le_sSup ⟨hYn, hYp⟩
    intro y hy
    refine hYJ fun x hx => ?_
    have h1 := inv_mem (show ⁅y, x⁆ ∈ Z from hy x hx)
    rwa [commutatorElement_inv] at h1
  have hVA : ⁅V, A⁆ ≠ ⊥ := by
    intro hbot
    have hCn : (centralizer (P : Set I)).Normal := ⟨fun c hc h p hp => by
      have hp' : h⁻¹ * p * h ∈ P := by
        have h1 := hPn.conj_mem p hp h⁻¹
        rwa [inv_inv] at h1
      have h1 := mem_centralizer_iff.1 hc _ hp'
      calc p * (h * c * h⁻¹) = h * ((h⁻¹ * p * h) * c) * h⁻¹ := by group
        _ = h * (c * (h⁻¹ * p * h)) * h⁻¹ := by rw [h1]
        _ = h * c * h⁻¹ * p := by group⟩
    have hYn : (centralizer (P : Set I) ⊓ commIn P (J : Set I)).Normal := by
      have := commIn_normal P J
      infer_instance
    have hYp : IsPGroup 2 ↥(centralizer (P : Set I) ⊓ commIn P (J : Set I)) := by
      refine isPGroup_two_of_odd_mem hJp fun y hy hodd => ?_
      obtain ⟨hyC, hyJ⟩ := mem_inf.1 hy
      have hyP : ∀ p ∈ P, y * p = p * y := fun p hp => (mem_centralizer_iff.1 hyC p hp).symm
      have hyJ' := commute_of_odd_orderOf hodd hJp hPJ hyP fun x hx => by
        have h1 := inv_mem (hyJ x hx)
        rw [commutatorElement_inv] at h1
        exact h1
      exact hJC (mem_centralizer_iff.2 fun h hh => (hyJ' h hh).symm)
    have hYJ : centralizer (P : Set I) ⊓ commIn P (J : Set I) ≤ J :=
      (le_sSup ⟨hYn, hYp⟩ : _ ≤ pCore 2 I).trans hJ'.ge
    have hVY : V ≤ centralizer (P : Set I) ⊓ commIn P (J : Set I) := by
      intro v hv
      refine mem_inf.2 ⟨?_, fun j hj => ?_⟩
      · have hle : P ≤ centralizer ({v} : Set I) := by
          rw [hPdef]
          refine sup_le (fun b hb => ?_) (fun a ha => ?_)
          · rw [mem_centralizer_singleton_iff]
            exact hVab b (hBV hb) v hv
          · rw [mem_centralizer_singleton_iff]
            have h1 : ⁅v, a⁆ = 1 := by
              have h2 := commutator_mem_commutator hv ha
              rw [hbot] at h2
              exact mem_bot.1 h2
            exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
        exact mem_centralizer_iff.2 fun p hp => mem_centralizer_singleton_iff.1 (hle hp)
      · rw [← commutatorElement_inv]
        exact inv_mem (hBP (hVJB v hv j hj))
    have hVJ : V ≤ J := hVY.trans hYJ
    have hWJ : conjugate V g ≤ J := fun x hx => by
      have h1 := hVJ (mem_conjugate_iff.1 hx)
      have h2 := hJn.conj_mem _ h1 g⁻¹
      simpa [mul_assoc] using h2
    have hJtop : J = ⊤ := by
      rw [eq_top_iff, ← hI]
      exact sup_le hVJ hWJ
    have hTtop : (T : Subgroup I) = ⊤ := by
      rw [eq_top_iff, ← hJtop]
      exact hJT
    have hVn : normalizer (V : Set I) = ⊤ := by
      rw [eq_top_iff, ← hTtop]
      exact hTV
    have hVg : conjugate V g = V := conjugate_of_mem_normalizer (by rw [hVn]; exact mem_top g)
    rw [hVg, sup_idem] at hI
    exact hVI.ne hI
  have hpow : ∀ H K : Subgroup I, IsPGroup 2 K → ∃ e, H.relIndex K = 2 ^ e := by
    intro H K hK
    obtain ⟨n, hn⟩ := hK.exists_card_eq
    have h1 : H.relIndex K ∣ 2 ^ n := by
      rw [← hn]
      exact relIndex_dvd_card (H := H) (K := K)
    obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    exact ⟨e, he⟩
  have hlog : Nat.log 2 ((V ⊓ centralizer (A : Set I)).relIndex V) ≤
      Nat.log 2 (Z.relIndex A) + Nat.log 2 (B.relIndex V) := by
    have hZC : Z ≤ V ⊓ centralizer (A : Set I) :=
      le_inf hZV fun z hz => mem_centralizer_iff.2 fun a _ => mem_center_iff.1 (hZcen hz) a
    have h2 : Z.relIndex V = Z.relIndex B * B.relIndex V :=
      (relIndex_mul_relIndex Z B V hZB hBV).symm
    obtain ⟨a, ha⟩ := hpow Z A (hJp.to_le hAJ)
    obtain ⟨b, hb⟩ := hpow B V hVp
    have hZVpow : Z.relIndex V = 2 ^ (a + b) := by rw [h2, ← hrel, ha, hb, pow_add]
    have h1 : (V ⊓ centralizer (A : Set I)).relIndex V ≤ Z.relIndex V :=
      Nat.le_of_dvd (by rw [hZVpow]; positivity) (relIndex_dvd_of_le_left V hZC)
    calc Nat.log 2 ((V ⊓ centralizer (A : Set I)).relIndex V) ≤ Nat.log 2 (Z.relIndex V) :=
          Nat.log_mono_right h1
      _ = a + b := by rw [hZVpow, Nat.log_pow (by norm_num)]
      _ = Nat.log 2 (Z.relIndex A) + Nat.log 2 (B.relIndex V) := by
          rw [ha, hb, Nat.log_pow (by norm_num), Nat.log_pow (by norm_num)]
  exact ⟨hAB, hPn, hZcen, ⟨hZB, hZA, hBA, hPcomm, hPsq⟩, hrel, hcubic, hVA, hCAV, hJIP, hCPZ,
    hlog⟩

end CFSG.Quasithin.SteinbergBS
