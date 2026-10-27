module

public import CFSG.RankThree.PartTwo.Sec18.Item187F6Weights
public import CFSG.LocalAnalysis.SignalizerFunctor.CoprimeGeneration

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open scoped commutatorElement Pointwise

variable {V : Type} [Group V] [Finite V]

private theorem hypComm_of_sq (hV : ∀ v : V, v * v = 1) (a b : V) : a * b = b * a := by
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hV a)
  have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hV b)
  have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hV _)
  rw [mul_inv_rev, ha, hb] at hab
  exact hab.symm

private theorem isMulCommutative_of_sq (hV : ∀ v : V, v * v = 1) : IsMulCommutative V :=
  ⟨⟨fun a b => hypComm_of_sq hV a b⟩⟩

private theorem normal_of_sq (hV : ∀ v : V, v * v = 1) (K : Subgroup V) : K.Normal := by
  haveI := isMulCommutative_of_sq hV
  infer_instance

private theorem mem_fix_iff (L : Subgroup (MulAut V)) (v : V) : v ∈ Fix L ↔ ∀ f ∈ L, f v = v :=
  ⟨fun h f hf => (FixedPoints.mem_subgroup _ _ _).mp h ⟨f, hf⟩,
    fun h => (FixedPoints.mem_subgroup _ _ _).mpr fun m => h m.1 m.2⟩

private theorem fix_anti {L₁ L₂ : Subgroup (MulAut V)} (h : L₁ ≤ L₂) : Fix L₂ ≤ Fix L₁ := by
  intro v hv
  rw [mem_fix_iff] at hv ⊢
  exact fun f hf => hv f (h hf)

private theorem fix_sup_le (L₁ L₂ : Subgroup (MulAut V)) : Fix L₁ ⊓ Fix L₂ ≤ Fix (L₁ ⊔ L₂) := by
  intro v hv
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hv
  rw [mem_fix_iff] at h1 h2 ⊢
  have hst : L₁ ⊔ L₂ ≤ MulAction.stabilizer (MulAut V) v :=
    sup_le (fun f hf => MulAction.mem_stabilizer_iff.mpr (h1 f hf))
      (fun f hf => MulAction.mem_stabilizer_iff.mpr (h2 f hf))
  exact fun f hf => MulAction.mem_stabilizer_iff.mp (hst hf)

private theorem five_dvd_of_zpow_mem {H : Subgroup (MulAut V)} {x : MulAut V} (hx5 : x ^ 5 = 1)
    (hxH : x ∉ H) {m : ℤ} (hm : x ^ m ∈ H) : (5 : ℤ) ∣ m := by
  by_contra hnd
  have h5 : x ^ (5 : ℤ) = 1 := by
    rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact hx5
  have key : ∃ k t : ℤ, m * k = 1 + 5 * t := by
    rcases (by omega : m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4) with h | h | h | h
    · exact ⟨1, (m - 1) / 5, by omega⟩
    · exact ⟨3, (3 * m - 1) / 5, by omega⟩
    · exact ⟨2, (2 * m - 1) / 5, by omega⟩
    · exact ⟨4, (4 * m - 1) / 5, by omega⟩
  obtain ⟨k, t, hkt⟩ := key
  have hx_eq : (x ^ m) ^ k = x := by
    rw [← zpow_mul, hkt, zpow_add, zpow_mul, h5, one_zpow, mul_one, zpow_one]
  have hmem : (x ^ m) ^ k ∈ H := Subgroup.zpow_mem H hm k
  rw [hx_eq] at hmem
  exact hxH hmem

private def hypZT (H : Subgroup (MulAut V)) (x : MulAut V) (hc : ∀ h ∈ H, h * x = x * h) :
    Subgroup (MulAut V) where
  carrier := {w | ∃ h ∈ H, ∃ k : ℤ, w = h * x ^ k}
  mul_mem' := by
    rintro _ _ ⟨h, hh, k, rfl⟩ ⟨h', hh', k', rfl⟩
    have e1 : x ^ k * h' = h' * x ^ k := (Commute.zpow_left (hc h' hh').symm k).eq
    refine ⟨h * h', H.mul_mem hh hh', k + k', ?_⟩
    calc h * x ^ k * (h' * x ^ k') = h * (x ^ k * h') * x ^ k' := by simp only [mul_assoc]
      _ = h * (h' * x ^ k) * x ^ k' := by rw [e1]
      _ = h * h' * (x ^ k * x ^ k') := by simp only [mul_assoc]
      _ = h * h' * x ^ (k + k') := by rw [zpow_add]
  one_mem' := ⟨1, H.one_mem, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨h, hh, k, rfl⟩
    refine ⟨h⁻¹, H.inv_mem hh, -k, ?_⟩
    have e1 : (x ^ k)⁻¹ * h⁻¹ = h⁻¹ * (x ^ k)⁻¹ :=
      ((Commute.zpow_left (hc h⁻¹ (H.inv_mem hh)).symm k).inv_left).eq
    rw [mul_inv_rev, zpow_neg, e1]

private theorem mem_sup_zpowers_of_comm {H : Subgroup (MulAut V)} {x : MulAut V}
    (hc : ∀ h ∈ H, h * x = x * h) {w : MulAut V} (hw : w ∈ H ⊔ Subgroup.zpowers x) :
    ∃ h ∈ H, ∃ k : ℤ, w = h * x ^ k := by
  have hle : H ⊔ Subgroup.zpowers x ≤ hypZT H x hc :=
    sup_le (fun h hh => ⟨h, hh, 0, by simp⟩)
      (Subgroup.zpowers_le.mpr ⟨1, H.one_mem, 1, by simp⟩)
  exact hle hw

private theorem hyper_sup_zpowers_eq {E H : Subgroup (MulAut V)} (hHE : H ≤ E) (hH : H.relIndex E = 5)
    {x : MulAut V} (hxE : x ∈ E) (hxH : x ∉ H) : H ⊔ Subgroup.zpowers x = E := by
  have h1 : H ≤ H ⊔ Subgroup.zpowers x := le_sup_left
  have h2 : H ⊔ Subgroup.zpowers x ≤ E := sup_le hHE (Subgroup.zpowers_le.mpr hxE)
  have hm := Subgroup.relIndex_mul_relIndex H (H ⊔ Subgroup.zpowers x) E h1 h2
  rw [hH] at hm
  rcases Nat.prime_five.eq_one_or_self_of_dvd _ (⟨_, hm.symm⟩ : _ ∣ 5) with h | h
  · exfalso
    have hle : H ⊔ Subgroup.zpowers x ≤ H := Subgroup.relIndex_eq_one.mp h
    exact hxH (hle ((le_sup_right : Subgroup.zpowers x ≤ H ⊔ Subgroup.zpowers x)
      (Subgroup.mem_zpowers x)))
  · have h' : (H ⊔ Subgroup.zpowers x).relIndex E = 1 := by
      rw [h] at hm
      omega
    exact le_antisymm h2 (Subgroup.relIndex_eq_one.mp h')

private theorem exists_mem_not_mem_of_relIndex {E H : Subgroup (MulAut V)} (hH : H.relIndex E = 5) :
    ∃ x ∈ E, x ∉ H := by
  by_contra hc
  push Not at hc
  have hEH : E ≤ H := fun x hx => hc x hx
  have h1 : H.relIndex E = 1 := Subgroup.relIndex_eq_one.mpr hEH
  omega

private theorem zt_fix {z : MulAut V} {c m : V} (hV : ∀ v : V, v * v = 1) (hz5 : z ^ 5 = 1)
    (hzc : z c = c) (hzm : z m = c * m) : z m = m := by
  have h2 : z (z m) = m := by
    rw [hzm, map_mul, hzc, hzm, ← mul_assoc, hV c, one_mul]
  have h4 : z (z (z (z m))) = m := by
    rw [h2, h2]
  have hz5m : z (z (z (z (z m)))) = m := by
    have h := congrArg (fun f : MulAut V => f m) hz5
    simpa [pow_succ, MulAut.mul_apply] using h
  rw [h4] at hz5m
  exact hz5m

private theorem smul_mem_fix_of_comm {E H : Subgroup (MulAut V)}
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hHE : H ≤ E) {g : MulAut V} (hg : g ∈ E)
    {v : V} (hv : v ∈ Fix H) : g v ∈ Fix H := by
  rw [mem_fix_iff] at hv ⊢
  intro f hf
  have hfg : f * g = g * f := hEab f (hHE hf) g hg
  calc f (g v) = (f * g) v := (MulAut.mul_apply V f g v).symm
    _ = (g * f) v := by rw [hfg]
    _ = g (f v) := MulAut.mul_apply V g f v
    _ = g v := by rw [hv f hf]

private theorem eq_of_le_hyper {E H K : Subgroup (MulAut V)} (hHK : H ≤ K) (hKE : K ≤ E)
    (hH : H.relIndex E = 5) (hK : K.relIndex E = 5) : H = K := by
  have hm := Subgroup.relIndex_mul_relIndex H K E hHK hKE
  rw [hK, hH] at hm
  have h1 : H.relIndex K = 1 := by omega
  exact le_antisymm hHK (Subgroup.relIndex_eq_one.mp h1)

private theorem eq_of_not_le_hyper {E H K : Subgroup (MulAut V)} (hHK : H ≤ K) (hKE : K ≤ E)
    (hH : H.relIndex E = 5) (hnot : ¬ K ≤ H) : K = E := by
  have hm := Subgroup.relIndex_mul_relIndex H K E hHK hKE
  rw [hH] at hm
  rcases Nat.prime_five.eq_one_or_self_of_dvd _ (⟨_, hm.symm⟩ : _ ∣ 5) with h | h
  · exact absurd (Subgroup.relIndex_eq_one.mp h) hnot
  · have h' : K.relIndex E = 1 := by
      rw [h] at hm
      omega
    exact le_antisymm hKE (Subgroup.relIndex_eq_one.mp h')

private theorem sup_eq_top_of_ne {E H₁ H₂ : Subgroup (MulAut V)} (hH₁E : H₁ ≤ E)
    (hH₁ : H₁.relIndex E = 5) (hH₂E : H₂ ≤ E) (hH₂ : H₂.relIndex E = 5) (hne : H₁ ≠ H₂) :
    H₁ ⊔ H₂ = E := by
  refine eq_of_not_le_hyper le_sup_left (sup_le hH₁E hH₂E) hH₁ ?_
  intro h
  exact hne (eq_of_le_hyper ((le_sup_right : H₂ ≤ H₁ ⊔ H₂).trans h) hH₁E hH₂ hH₁).symm

private theorem fix_inf_eq_fix_of_ne {E H₁ H₂ : Subgroup (MulAut V)} (hH₁E : H₁ ≤ E)
    (hH₁ : H₁.relIndex E = 5) (hH₂E : H₂ ≤ E) (hH₂ : H₂.relIndex E = 5) (hne : H₁ ≠ H₂) :
    Fix H₁ ⊓ Fix H₂ = Fix E := by
  apply le_antisymm
  · have h := fix_sup_le H₁ H₂
    rw [sup_eq_top_of_ne hH₁E hH₁ hH₂E hH₂ hne] at h
    exact h
  · exact le_inf (fix_anti hH₁E) (fix_anti hH₂E)

private theorem exists_mem_not_mem_two {E H₁ H₂ H₃ : Subgroup (MulAut V)} (hH₁E : H₁ ≤ E)
    (hH₁ : H₁.relIndex E = 5) (hH₂E : H₂ ≤ E) (hH₂ : H₂.relIndex E = 5)
    (hH₃E : H₃ ≤ E) (hH₃ : H₃.relIndex E = 5) (h31 : H₃ ≠ H₁) (h32 : H₃ ≠ H₂) :
    ∃ z ∈ H₃, z ∉ H₁ ∧ z ∉ H₂ := by
  have hn1 : ¬ H₃ ≤ H₁ := fun h => h31 (eq_of_le_hyper h hH₁E hH₃ hH₁)
  have hn2 : ¬ H₃ ≤ H₂ := fun h => h32 (eq_of_le_hyper h hH₂E hH₃ hH₂)
  obtain ⟨a, ha3, ha1⟩ := SetLike.not_le_iff_exists.mp hn1
  obtain ⟨b, hb3, hb2⟩ := SetLike.not_le_iff_exists.mp hn2
  by_contra hcon
  have key : ∀ z ∈ H₃, z ∈ H₁ ∨ z ∈ H₂ := fun z hz3 => by
    by_contra hnot
    exact hcon ⟨z, hz3, fun h => hnot (Or.inl h), fun h => hnot (Or.inr h)⟩
  have ha2 : a ∈ H₂ := (key a ha3).resolve_left ha1
  have hb1 : b ∈ H₁ := (key b hb3).resolve_right hb2
  rcases key (a * b) (H₃.mul_mem ha3 hb3) with hz1 | hz2
  · have h := H₁.mul_mem hz1 (H₁.inv_mem hb1)
    rw [mul_inv_cancel_right] at h
    exact ha1 h
  · have h := H₂.mul_mem (H₂.inv_mem ha2) hz2
    rw [inv_mul_cancel_left] at h
    exact hb2 h

private theorem mul_eq_of_mul_eq (hV : ∀ v : V, v * v = 1) {p q a b : V} (h : p * q = a * b) :
    p * a = b * q := by
  haveI : Std.Commutative (α := V) (· * ·) := ⟨fun x y => hypComm_of_sq hV x y⟩
  haveI : Std.Associative (α := V) (· * ·) := ⟨mul_assoc⟩
  calc p * a = p * a * (q * q) := by rw [hV q, mul_one]
    _ = (p * q) * (a * q) := by ac_rfl
    _ = (a * b) * (a * q) := by rw [h]
    _ = (a * a) * (b * q) := by ac_rfl
    _ = b * q := by rw [hV a, one_mul]

private theorem fix_sup_inf_eq {E H₁ H₂ H₃ : Subgroup (MulAut V)} (hV : ∀ v : V, v * v = 1)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE5 : ∀ x ∈ E, x ^ 5 = 1)
    (hH₁E : H₁ ≤ E) (hH₁ : H₁.relIndex E = 5) (hH₂E : H₂ ≤ E) (hH₂ : H₂.relIndex E = 5)
    (hH₃E : H₃ ≤ E) (hH₃ : H₃.relIndex E = 5) (h12 : H₁ ≠ H₂) (h31 : H₃ ≠ H₁)
    (h32 : H₃ ≠ H₂) :
    (Fix H₁ ⊔ Fix H₂) ⊓ Fix H₃ = Fix E := by
  haveI := normal_of_sq hV (Fix H₂)
  apply le_antisymm
  · intro v hv
    obtain ⟨hv12, hv3⟩ := Subgroup.mem_inf.mp hv
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp hv12
    obtain ⟨z, hz3, hz1, hz2⟩ := exists_mem_not_mem_two hH₁E hH₁ hH₂E hH₂ hH₃E hH₃ h31 h32
    have hzE : z ∈ E := hH₃E hz3
    have hz5 : z ^ 5 = 1 := hE5 z hzE
    have hzv : z v = v := (mem_fix_iff H₃ v).mp hv3 z hz3
    rw [← hab, map_mul] at hzv
    have hza : z a ∈ Fix H₁ := smul_mem_fix_of_comm hEab hH₁E hzE ha
    have hzb : z b ∈ Fix H₂ := smul_mem_fix_of_comm hEab hH₂E hzE hb
    have hkey : z a * a = b * z b := mul_eq_of_mul_eq hV hzv
    have hu1 : z a * a ∈ Fix H₁ := (Fix H₁).mul_mem hza ha
    have hu2 : z a * a ∈ Fix H₂ := by
      rw [hkey]
      exact (Fix H₂).mul_mem hb hzb
    have hu : z a * a ∈ Fix E := by
      have h := Subgroup.mem_inf.mpr ⟨hu1, hu2⟩
      rwa [fix_inf_eq_fix_of_ne hH₁E hH₁ hH₂E hH₂ h12] at h
    have hzu : z (z a * a) = z a * a := (mem_fix_iff E _).mp hu z hzE
    have hzm : z a = (z a * a) * a := by rw [mul_assoc, hV a, mul_one]
    have hza_fix : z a = a := zt_fix hV hz5 hzu hzm
    rw [hza_fix] at hzv
    have hzb_fix : z b = b := mul_left_cancel hzv
    have ha_fix : a ∈ Fix E := by
      have h := fix_sup_le H₁ (Subgroup.zpowers z)
        (Subgroup.mem_inf.mpr ⟨ha, mem_fix_zpowers_iff.mpr hza_fix⟩)
      rwa [hyper_sup_zpowers_eq hH₁E hH₁ hzE hz1] at h
    have hb_fix : b ∈ Fix E := by
      have h := fix_sup_le H₂ (Subgroup.zpowers z)
        (Subgroup.mem_inf.mpr ⟨hb, mem_fix_zpowers_iff.mpr hzb_fix⟩)
      rwa [hyper_sup_zpowers_eq hH₂E hH₂ hzE hz2] at h
    rw [← hab]
    exact (Fix E).mul_mem ha_fix hb_fix
  · exact le_inf (le_sup_of_le_left (fix_anti hH₁E)) (fix_anti hH₃E)

private theorem relIndex_sup_eq_mul {A X M : Subgroup V} [X.Normal] (hAX : A ≤ X) (hXM : X ⊓ M = A) :
    A.relIndex (X ⊔ M) = A.relIndex X * A.relIndex M := by
  have h1 : X.relIndex M = A.relIndex M := by
    rw [← hXM, Subgroup.inf_relIndex_right]
  rw [← Subgroup.relIndex_mul_relIndex A X (X ⊔ M) hAX le_sup_left, Subgroup.relIndex_sup_left,
    h1]

private theorem relIndex_le_index_of_inf_eq {P C A : Subgroup V} (hPC : P ⊓ C = A) :
    A.relIndex P ≤ C.index := by
  rw [← hPC]
  calc (P ⊓ C).relIndex P ≤ P.relIndex P * C.relIndex P := Subgroup.relIndex_inf_le
    _ = C.relIndex P := by rw [Subgroup.relIndex_self, one_mul]
    _ ≤ C.relIndex ⊤ := Subgroup.relIndex_le_of_le_right le_top (by
        rw [Subgroup.relIndex_top_right]
        exact Subgroup.index_ne_zero_of_finite)
    _ = C.index := Subgroup.relIndex_top_right C

private theorem card_fix_modEq_of_fixed (hV : ∀ v : V, v * v = 1) {E H : Subgroup (MulAut V)}
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hHE : H ≤ E) {x : MulAut V} (hxE : x ∈ E)
    (hx5 : x ^ 5 = 1) (hfix : ∀ v : V, v ∈ Fix H → x v = v → v ∈ Fix E) :
    Nat.card (Fix H) ≡ Nat.card (Fix E) [MOD 5] := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hP : IsPGroup 5 (Subgroup.zpowers x) := by
    have hdiv : orderOf x ∣ 5 := orderOf_dvd_of_pow_eq_one hx5
    rcases (Nat.dvd_prime Nat.prime_five).mp hdiv with hi | hi
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, hi]; norm_num)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hi]; norm_num)
  let S : SubMulAction (Subgroup.zpowers x) V :=
    { carrier := (Fix H : Set V)
      smul_mem' := fun c v hv => smul_mem_fix_of_comm hEab hHE
        (Subgroup.zpowers_le.mpr hxE c.2) hv }
  have hcard := hP.card_modEq_card_fixedPoints ↥S
  have h1 : Nat.card ↥S = Nat.card (Fix H) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v => Iff.rfl)
  have hto : ∀ p : MulAction.fixedPoints (Subgroup.zpowers x) ↥S, x p.1.1 = p.1.1 := fun p => by
    have h := congrArg Subtype.val
      (MulAction.mem_fixedPoints.mp p.2 ⟨x, Subgroup.mem_zpowers x⟩)
    simpa [MulAut.smul_def] using h
  have hinv : ∀ v : Fix E, ∀ g : Subgroup.zpowers x,
      g • (⟨v.1, fix_anti hHE v.2⟩ : ↥S) = ⟨v.1, fix_anti hHE v.2⟩ := by
    intro v g
    apply Subtype.ext
    show (g : MulAut V) v.1 = v.1
    exact (mem_fix_iff E v.1).mp v.2 g (Subgroup.zpowers_le.mpr hxE g.2)
  have h2 : Nat.card (MulAction.fixedPoints (Subgroup.zpowers x) ↥S) = Nat.card (Fix E) :=
    Nat.card_congr
      { toFun := fun p => ⟨p.1.1, hfix p.1.1 p.1.2 (hto p)⟩
        invFun := fun v => ⟨⟨v.1, fix_anti hHE v.2⟩, MulAction.mem_fixedPoints.mpr (hinv v)⟩
        left_inv := fun p => Subtype.ext (Subtype.ext rfl)
        right_inv := fun v => Subtype.ext rfl }
  rw [h1, h2] at hcard
  exact hcard

private theorem relIndex_fix_modEq_one (hV : ∀ v : V, v * v = 1) {E H : Subgroup (MulAut V)}
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hHE : H ≤ E) {x : MulAut V} (hxE : x ∈ E)
    (hx5 : x ^ 5 = 1) (hfix : ∀ v : V, v ∈ Fix H → x v = v → v ∈ Fix E) :
    (Fix E).relIndex (Fix H) ≡ 1 [MOD 5] := by
  have hcong := card_fix_modEq_of_fixed hV hEab hHE hxE hx5 hfix
  have hmul := Subgroup.relIndex_mul_card (Fix E) (Fix H)
  rw [inf_eq_left.mpr (fix_anti hHE)] at hmul
  obtain ⟨n, hn⟩ := card_V_eq_two_pow hV
  have hAdvd : Nat.card (Fix E) ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.card_subgroup_dvd_card (Fix E)
  have hcop : Nat.Coprime 5 (Nat.card (Fix E)) :=
    Nat.Coprime.coprime_dvd_right hAdvd (Nat.Coprime.pow_right n (by norm_num))
  have h1 : (Fix E).relIndex (Fix H) * Nat.card (Fix E) ≡ 1 * Nat.card (Fix E) [MOD 5] := by
    rw [one_mul, hmul]
    exact hcong
  exact Nat.ModEq.cancel_right_of_coprime hcop h1

private theorem sixteen_le_relIndex_of_active (hV : ∀ v : V, v * v = 1) {E H : Subgroup (MulAut V)}
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hHE : H ≤ E) {x : MulAut V} (hxE : x ∈ E)
    (hx5 : x ^ 5 = 1) (hfix : ∀ v : V, v ∈ Fix H → x v = v → v ∈ Fix E)
    (hact : ¬ Fix H ≤ Fix E) : 16 ≤ (Fix E).relIndex (Fix H) := by
  have hcong := relIndex_fix_modEq_one hV hEab hHE hxE hx5 hfix
  obtain ⟨n, hn⟩ := card_V_eq_two_pow hV
  have hdvd : (Fix E).relIndex (Fix H) ∣ 2 ^ n := by
    have hmul := Subgroup.relIndex_mul_card (Fix E) (Fix H)
    rw [inf_eq_left.mpr (fix_anti hHE)] at hmul
    have h1 : (Fix E).relIndex (Fix H) ∣ Nat.card (Fix H) := ⟨_, hmul.symm⟩
    rw [← hn]
    exact h1.trans (Subgroup.card_subgroup_dvd_card (Fix H))
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hmod : 2 ^ j % 5 = 1 := by
    rw [← hj]
    have h := hcong
    unfold Nat.ModEq at h
    simpa using h
  obtain ⟨k, hk⟩ := two_pow_eq_sixteen_pow_of_mod_five hmod
  have hne : (Fix E).relIndex (Fix H) ≠ 1 := by
    intro h1
    exact hact (Subgroup.relIndex_eq_one.mp h1)
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hne
    rw [hj, hk, pow_zero]
  calc 16 = 16 ^ 1 := (pow_one 16).symm
    _ ≤ 16 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 ^ j := hk.symm
    _ = (Fix E).relIndex (Fix H) := hj.symm

private theorem exists_not_mem_three {E H₁ H₂ H₃ : Subgroup (MulAut V)} (hH₁E : H₁ ≤ E)
    (hH₁ : H₁.relIndex E = 5) (hH₂E : H₂ ≤ E) (hH₂ : H₂.relIndex E = 5)
    (hH₃E : H₃ ≤ E) (hH₃ : H₃.relIndex E = 5) :
    ∃ y ∈ E, y ∉ H₁ ∧ y ∉ H₂ ∧ y ∉ H₃ := by
  haveI : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V ≃ V))
      (fun f g h => MulEquiv.ext fun v => congrArg (fun e : V ≃ V => e v) h)
  by_contra hcon
  have hcov : (E : Set (MulAut V)) ⊆
      (H₁ : Set (MulAut V)) ∪ (H₂ : Set (MulAut V)) ∪ (H₃ : Set (MulAut V)) := by
    intro y hy
    by_contra hn
    simp only [Set.mem_union, SetLike.mem_coe, not_or] at hn
    exact hcon ⟨y, hy, hn.1.1, hn.1.2, hn.2⟩
  have c1 := Subgroup.relIndex_mul_card H₁ E
  have c2 := Subgroup.relIndex_mul_card H₂ E
  have c3 := Subgroup.relIndex_mul_card H₃ E
  rw [inf_eq_left.mpr hH₁E, hH₁] at c1
  rw [inf_eq_left.mpr hH₂E, hH₂] at c2
  rw [inf_eq_left.mpr hH₃E, hH₃] at c3
  haveI : Nonempty E := ⟨1⟩
  have hpos : 0 < Nat.card E := Nat.card_pos
  have hc := Set.ncard_le_ncard hcov
  have hu1 := Set.ncard_union_le ((H₁ : Set (MulAut V)) ∪ (H₂ : Set (MulAut V)))
    (H₃ : Set (MulAut V))
  have hu2 := Set.ncard_union_le (H₁ : Set (MulAut V)) (H₂ : Set (MulAut V))
  have e0 : Nat.card E = (E : Set (MulAut V)).ncard := Nat.card_coe_set_eq _
  have e1 : Nat.card H₁ = (H₁ : Set (MulAut V)).ncard := Nat.card_coe_set_eq _
  have e2 : Nat.card H₂ = (H₂ : Set (MulAut V)).ncard := Nat.card_coe_set_eq _
  have e3 : Nat.card H₃ = (H₃ : Set (MulAut V)).ncard := Nat.card_coe_set_eq _
  omega

private theorem fix_zpowers_inf_sup_eq (hV : ∀ v : V, v * v = 1)
    {E H₂ H₃ : Subgroup (MulAut V)} {y : MulAut V}
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE5 : ∀ x ∈ E, x ^ 5 = 1)
    (hH₂E : H₂ ≤ E) (hH₂ : H₂.relIndex E = 5) (hH₃E : H₃ ≤ E) (hH₃ : H₃.relIndex E = 5)
    (h23 : H₂ ≠ H₃) (hyE : y ∈ E) (hy2 : y ∉ H₂) (hy3 : y ∉ H₃) :
    Fix (Subgroup.zpowers y) ⊓ (Fix H₂ ⊔ Fix H₃) = Fix E := by
  haveI := normal_of_sq hV (Fix H₃)
  apply le_antisymm
  · intro v hv
    obtain ⟨hvy, hv23⟩ := Subgroup.mem_inf.mp hv
    have hyv : y v = v := mem_fix_zpowers_iff.mp hvy
    obtain ⟨b, hb, c, hc, hbc⟩ := Subgroup.mem_sup_of_normal_right.mp hv23
    have hyb : y b ∈ Fix H₂ := smul_mem_fix_of_comm hEab hH₂E hyE hb
    have hyc : y c ∈ Fix H₃ := smul_mem_fix_of_comm hEab hH₃E hyE hc
    rw [← hbc, map_mul] at hyv
    have hkey : y b * b = c * y c := mul_eq_of_mul_eq hV hyv
    have hu : y b * b ∈ Fix E := by
      have h : y b * b ∈ Fix H₂ ⊓ Fix H₃ :=
        Subgroup.mem_inf.mpr ⟨(Fix H₂).mul_mem hyb hb, by rw [hkey]; exact (Fix H₃).mul_mem hc hyc⟩
      rwa [fix_inf_eq_fix_of_ne hH₂E hH₂ hH₃E hH₃ h23] at h
    have hyu : y (y b * b) = y b * b := (mem_fix_iff E _).mp hu y hyE
    have hybm : y b = (y b * b) * b := by rw [mul_assoc, hV b, mul_one]
    have hyb_fix : y b = b := zt_fix hV (hE5 y hyE) hyu hybm
    rw [hyb_fix] at hyv
    have hyc_fix : y c = c := mul_left_cancel hyv
    have hbE : b ∈ Fix E := by
      have h : b ∈ Fix H₂ ⊓ Fix (Subgroup.zpowers y) :=
        Subgroup.mem_inf.mpr ⟨hb, mem_fix_zpowers_iff.mpr hyb_fix⟩
      have h' := fix_sup_le H₂ (Subgroup.zpowers y) h
      rwa [hyper_sup_zpowers_eq hH₂E hH₂ hyE hy2] at h'
    have hcE : c ∈ Fix E := by
      have h : c ∈ Fix H₃ ⊓ Fix (Subgroup.zpowers y) :=
        Subgroup.mem_inf.mpr ⟨hc, mem_fix_zpowers_iff.mpr hyc_fix⟩
      have h' := fix_sup_le H₃ (Subgroup.zpowers y) h
      rwa [hyper_sup_zpowers_eq hH₃E hH₃ hyE hy3] at h'
    rw [← hbc]
    exact (Fix E).mul_mem hbE hcE
  · exact le_inf (fix_anti (Subgroup.zpowers_le.mpr hyE)) (le_sup_of_le_left (fix_anti hH₂E))

private theorem fix_sup_sup_zpowers_inf_eq (hV : ∀ v : V, v * v = 1)
    {E H₁ H₂ H₃ : Subgroup (MulAut V)} {y : MulAut V}
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE5 : ∀ x ∈ E, x ^ 5 = 1)
    (hH₁E : H₁ ≤ E) (hH₁ : H₁.relIndex E = 5) (hH₂E : H₂ ≤ E) (hH₂ : H₂.relIndex E = 5)
    (hH₃E : H₃ ≤ E) (hH₃ : H₃.relIndex E = 5) (h12 : H₁ ≠ H₂) (h13 : H₁ ≠ H₃) (h23 : H₂ ≠ H₃)
    (hyE : y ∈ E) (hy1 : y ∉ H₁) (hy2 : y ∉ H₂) (hy3 : y ∉ H₃) :
    (Fix H₁ ⊔ (Fix H₂ ⊔ Fix H₃)) ⊓ Fix (Subgroup.zpowers y) = Fix E := by
  haveI := normal_of_sq hV (Fix H₂ ⊔ Fix H₃)
  haveI := normal_of_sq hV (Fix H₃)
  apply le_antisymm
  · intro v hv
    obtain ⟨hvP, hvy⟩ := Subgroup.mem_inf.mp hv
    have hyv : y v = v := mem_fix_zpowers_iff.mp hvy
    obtain ⟨a, ha, m, hm, ham⟩ := Subgroup.mem_sup_of_normal_right.mp hvP
    have hym : y m ∈ Fix H₂ ⊔ Fix H₃ := by
      obtain ⟨b, hb, c, hc, hbc⟩ := Subgroup.mem_sup_of_normal_right.mp hm
      rw [← hbc, map_mul]
      exact (Fix H₂ ⊔ Fix H₃).mul_mem
        ((le_sup_left : Fix H₂ ≤ Fix H₂ ⊔ Fix H₃) (smul_mem_fix_of_comm hEab hH₂E hyE hb))
        ((le_sup_right : Fix H₃ ≤ Fix H₂ ⊔ Fix H₃) (smul_mem_fix_of_comm hEab hH₃E hyE hc))
    rw [← ham, map_mul] at hyv
    have hkey : y a * a = m * y m := mul_eq_of_mul_eq hV hyv
    have hδ1 : y a * a ∈ Fix H₁ :=
      (Fix H₁).mul_mem (smul_mem_fix_of_comm hEab hH₁E hyE ha) ha
    have hδ2 : y a * a ∈ Fix H₂ ⊔ Fix H₃ := by
      rw [hkey]
      exact (Fix H₂ ⊔ Fix H₃).mul_mem hm hym
    have hδ : y a * a ∈ Fix E := by
      have h : y a * a ∈ (Fix H₂ ⊔ Fix H₃) ⊓ Fix H₁ := Subgroup.mem_inf.mpr ⟨hδ2, hδ1⟩
      rwa [fix_sup_inf_eq hV hEab hE5 hH₂E hH₂ hH₃E hH₃ hH₁E hH₁ h23 h12 h13] at h
    have hzm : y a = (y a * a) * a := by rw [mul_assoc, hV a, mul_one]
    have hya : y a = a := zt_fix hV (hE5 y hyE) ((mem_fix_iff E _).mp hδ y hyE) hzm
    have hym_eq : y m = m := by
      have h1 : m * y m = m * m := by rw [← hkey, hya, hV a, hV m]
      exact mul_left_cancel h1
    have hmE : m ∈ Fix E := by
      have h : m ∈ Fix (Subgroup.zpowers y) ⊓ (Fix H₂ ⊔ Fix H₃) :=
        Subgroup.mem_inf.mpr ⟨mem_fix_zpowers_iff.mpr hym_eq, hm⟩
      rwa [fix_zpowers_inf_sup_eq hV hEab hE5 hH₂E hH₂ hH₃E hH₃ h23 hyE hy2 hy3] at h
    have haE : a ∈ Fix E := by
      have h : a ∈ Fix H₁ ⊓ Fix (Subgroup.zpowers y) :=
        Subgroup.mem_inf.mpr ⟨ha, mem_fix_zpowers_iff.mpr hya⟩
      have h' := fix_sup_le H₁ (Subgroup.zpowers y) h
      rwa [hyper_sup_zpowers_eq hH₁E hH₁ hyE hy1] at h'
    rw [← ham]
    exact (Fix E).mul_mem haE hmE
  · exact le_inf (le_sup_of_le_left (fix_anti hH₁E)) (fix_anti (Subgroup.zpowers_le.mpr hyE))

private theorem sixteen_of_active_hyper (hV : ∀ v : V, v * v = 1) {E H : Subgroup (MulAut V)}
    (hE5 : ∀ x ∈ E, x ^ 5 = 1) (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hHE : H ≤ E)
    (hH : H.relIndex E = 5) (hact : ¬ Fix H ≤ Fix E) : 16 ≤ (Fix E).relIndex (Fix H) := by
  obtain ⟨x, hxE, hxH⟩ := exists_mem_not_mem_of_relIndex hH
  refine sixteen_le_relIndex_of_active hV hEab hHE hxE (hE5 x hxE) ?_ hact
  intro v hv hxv
  have h := fix_sup_le H (Subgroup.zpowers x)
    (Subgroup.mem_inf.mpr ⟨hv, mem_fix_zpowers_iff.mpr hxv⟩)
  rwa [hyper_sup_zpowers_eq hHE hH hxE hxH] at h

private theorem exists_two_pow_twelve_of_three (hV : ∀ v : V, v * v = 1)
    {E H₁ H₂ H₃ : Subgroup (MulAut V)}
    (hE5 : ∀ x ∈ E, x ^ 5 = 1) (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hH₁E : H₁ ≤ E) (hH₁ : H₁.relIndex E = 5) (hH₂E : H₂ ≤ E) (hH₂ : H₂.relIndex E = 5)
    (hH₃E : H₃ ≤ E) (hH₃ : H₃.relIndex E = 5) (h12 : H₁ ≠ H₂) (h13 : H₁ ≠ H₃) (h23 : H₂ ≠ H₃)
    (ha₁ : ¬ Fix H₁ ≤ Fix E) (ha₂ : ¬ Fix H₂ ≤ Fix E) (ha₃ : ¬ Fix H₃ ≤ Fix E) :
    ∃ y ∈ E, 2 ^ 12 ≤ (Fix (Subgroup.zpowers y)).index := by
  obtain ⟨y, hyE, hy1, hy2, hy3⟩ := exists_not_mem_three hH₁E hH₁ hH₂E hH₂ hH₃E hH₃
  refine ⟨y, hyE, ?_⟩
  haveI := normal_of_sq hV (Fix H₁)
  haveI := normal_of_sq hV (Fix H₂)
  haveI := normal_of_sq hV (Fix H₃)
  have hP := fix_sup_sup_zpowers_inf_eq hV hEab hE5 hH₁E hH₁ hH₂E hH₂ hH₃E hH₃ h12 h13 h23
    hyE hy1 hy2 hy3
  have hbound := relIndex_le_index_of_inf_eq hP
  have hX : Fix H₁ ⊓ (Fix H₂ ⊔ Fix H₃) = Fix E := by
    rw [inf_comm]
    exact fix_sup_inf_eq hV hEab hE5 hH₂E hH₂ hH₃E hH₃ hH₁E hH₁ h23 h12 h13
  have hprod1 := relIndex_sup_eq_mul (M := Fix H₂ ⊔ Fix H₃) (fix_anti hH₁E) hX
  have hprod2 := relIndex_sup_eq_mul (M := Fix H₃) (fix_anti hH₂E)
    (fix_inf_eq_fix_of_ne hH₂E hH₂ hH₃E hH₃ h23)
  have e1 := sixteen_of_active_hyper hV hE5 hEab hH₁E hH₁ ha₁
  have e2 := sixteen_of_active_hyper hV hE5 hEab hH₂E hH₂ ha₂
  have e3 := sixteen_of_active_hyper hV hE5 hEab hH₃E hH₃ ha₃
  have hlow : 16 ^ 3 ≤ (Fix E).relIndex (Fix H₁ ⊔ (Fix H₂ ⊔ Fix H₃)) := by
    rw [hprod1, hprod2]
    calc 16 ^ 3 = 16 * (16 * 16) := by norm_num
      _ ≤ (Fix E).relIndex (Fix H₁) * ((Fix E).relIndex (Fix H₂) * (Fix E).relIndex (Fix H₃)) :=
          Nat.mul_le_mul e1 (Nat.mul_le_mul e2 e3)
  calc 2 ^ 12 = 16 ^ 3 := by norm_num
    _ ≤ (Fix E).relIndex (Fix H₁ ⊔ (Fix H₂ ⊔ Fix H₃)) := hlow
    _ ≤ (Fix (Subgroup.zpowers y)).index := hbound

private theorem index_dvd_five_of_cyclic {G : Type*} [Group G] (hG : ∀ g : G, g ^ 5 = 1)
    (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)] : N.index ∣ 5 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G ⧸ N)
  rw [Subgroup.index, ← orderOf_eq_card_of_forall_mem_zpowers hg]
  obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective g
  apply orderOf_dvd_of_pow_eq_one
  rw [← QuotientGroup.mk_pow, hG e, QuotientGroup.mk_one]

private theorem exists_active_hyper (hV : ∀ v : V, v * v = 1) {E : Subgroup (MulAut V)}
    (hE5 : ∀ x ∈ E, x ^ 5 = 1) (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hEne : E ≠ ⊥) :
    ∃ H : Subgroup (MulAut V), H ≤ E ∧ H.relIndex E = 5 ∧ ¬ Fix H ≤ Fix E := by
  haveI : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V ≃ V))
      (fun f g h => MulEquiv.ext fun v => congrArg (fun e : V ≃ V => e v) h)
  by_contra hcon
  have hinact : ∀ H : Subgroup (MulAut V), H ≤ E → H.relIndex E = 5 → Fix H ≤ Fix E := by
    intro H hHE hH
    by_contra h
    exact hcon ⟨H, hHE, hH, h⟩
  letI : CommGroup E :=
    { (inferInstance : Group E) with mul_comm := fun a b => Subtype.ext (hEab a a.2 b b.2) }
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hG : ∀ g : E, g ^ 5 = 1 := fun g => Subtype.ext (by simpa using hE5 g.1 g.2)
  have hpg : IsPGroup 5 E := fun g => ⟨1, by simpa using hG g⟩
  obtain ⟨n, hn⟩ := card_V_eq_two_pow hV
  have hcop : Nat.Coprime 5 (Nat.card V) := by
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hgen := CFSG.SignalizerFunctor.Helpers.coprime_cyclic_quotient_generation 5
    Nat.prime_five E hpg V hcop
  have hle : (⊤ : Subgroup V) ≤ Fix E := by
    rw [← hgen]
    refine iSup_le fun A' => iSup_le fun hcyc => ?_
    have hdvd : A'.index ∣ 5 := index_dvd_five_of_cyclic hG A'
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h5
    · have htop : A' = ⊤ := Subgroup.index_eq_one.mp h1
      subst htop
      intro v hv
      rw [mem_fix_iff]
      intro f hf
      exact (FixedPoints.mem_subgroup _ _ _).mp hv ⟨⟨f, hf⟩, Subgroup.mem_top _⟩
    · have hH'E : A'.map E.subtype ≤ E := by
        intro w hw
        obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.mp hw
        exact a.2
      have hsub : (A'.map E.subtype).subgroupOf E = A' := by
        ext a
        rw [Subgroup.mem_subgroupOf]
        constructor
        · intro h
          obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp h
          have hab : b = a := Subtype.ext hba
          rw [← hab]
          exact hb
        · intro h
          exact Subgroup.mem_map.mpr ⟨a, h, rfl⟩
      have hH'idx : (A'.map E.subtype).relIndex E = 5 := by
        rw [Subgroup.relIndex, hsub]
        exact h5
      have hact := hinact _ hH'E hH'idx
      intro v hv
      apply hact
      rw [mem_fix_iff]
      intro f hf
      obtain ⟨a, ha, hfa⟩ := Subgroup.mem_map.mp hf
      have h := (FixedPoints.mem_subgroup _ _ _).mp hv ⟨a, ha⟩
      rw [← hfa]
      exact h
  refine hEne (eq_bot_iff.mpr fun x hx => ?_)
  rw [Subgroup.mem_bot]
  apply MulEquiv.ext
  intro v
  have hv : v ∈ Fix E := hle (Subgroup.mem_top v)
  rw [mem_fix_iff] at hv
  rw [MulAut.one_apply]
  exact hv x hx

private def conjSub (d : MulAut V) (H : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  H.map (MulAut.conj d).toMonoidHom

private theorem conj_hom_apply (d h : MulAut V) :
    (MulAut.conj d).toMonoidHom h = d * h * d⁻¹ :=
  rfl

private theorem mem_conjSub {d g : MulAut V} {H : Subgroup (MulAut V)} :
    g ∈ conjSub d H ↔ ∃ h ∈ H, d * h * d⁻¹ = g := by
  unfold conjSub
  rw [Subgroup.mem_map]
  simp only [conj_hom_apply]

private theorem conjSub_mul (a b : MulAut V) (H : Subgroup (MulAut V)) :
    conjSub (a * b) H = conjSub a (conjSub b H) := by
  ext g
  constructor
  · intro hg
    obtain ⟨h, hh, rfl⟩ := mem_conjSub.mp hg
    exact mem_conjSub.mpr ⟨b * h * b⁻¹, mem_conjSub.mpr ⟨h, hh, rfl⟩, by group⟩
  · intro hg
    obtain ⟨k, hk, hkg⟩ := mem_conjSub.mp hg
    obtain ⟨h, hh, rfl⟩ := mem_conjSub.mp hk
    exact mem_conjSub.mpr ⟨h, hh, by rw [← hkg]; group⟩

private theorem conjSub_one (H : Subgroup (MulAut V)) : conjSub 1 H = H := by
  ext g
  constructor
  · intro hg
    obtain ⟨h, hh, rfl⟩ := mem_conjSub.mp hg
    simpa using hh
  · intro hg
    exact mem_conjSub.mpr ⟨g, hg, by simp⟩

private theorem conjSub_inv_conjSub (a : MulAut V) (H : Subgroup (MulAut V)) :
    conjSub a⁻¹ (conjSub a H) = H := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

private theorem conjSub_conjSub_inv (a : MulAut V) (H : Subgroup (MulAut V)) :
    conjSub a (conjSub a⁻¹ H) = H := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

private def stabSub (D H : Subgroup (MulAut V)) : Subgroup (MulAut V) where
  carrier := {d | d ∈ D ∧ conjSub d H = H}
  mul_mem' := fun {a b} ha hb => ⟨D.mul_mem ha.1 hb.1, by rw [conjSub_mul, hb.2, ha.2]⟩
  one_mem' := ⟨D.one_mem, conjSub_one H⟩
  inv_mem' := fun {a} ha => ⟨D.inv_mem ha.1, by
    calc conjSub a⁻¹ H = conjSub a⁻¹ (conjSub a H) := by rw [ha.2]
      _ = H := conjSub_inv_conjSub a H⟩

private theorem mem_stabSub {D H : Subgroup (MulAut V)} {d : MulAut V} :
    d ∈ stabSub D H ↔ d ∈ D ∧ conjSub d H = H :=
  Iff.rfl

private theorem mem_fix_conjSub (d : MulAut V) (H : Subgroup (MulAut V)) (v : V) :
    v ∈ Fix (conjSub d H) ↔ d⁻¹ v ∈ Fix H := by
  rw [mem_fix_iff, mem_fix_iff]
  constructor
  · intro h f hf
    have h1 : d (f (d⁻¹ v)) = v := by
      have := h (d * f * d⁻¹) (mem_conjSub.mpr ⟨f, hf, rfl⟩)
      rwa [MulAut.mul_apply, MulAut.mul_apply] at this
    have h2 : d⁻¹ (d (f (d⁻¹ v))) = d⁻¹ v := congrArg (fun z => d⁻¹ z) h1
    rwa [MulAut.inv_apply_self] at h2
  · intro h g hg
    obtain ⟨f, hf, rfl⟩ := mem_conjSub.mp hg
    have h1 : f (d⁻¹ v) = d⁻¹ v := h f hf
    rw [MulAut.mul_apply, MulAut.mul_apply, h1, MulAut.apply_inv_self]

private theorem conj_mem_of_normalizer {E : Subgroup (MulAut V)} {d : MulAut V}
    (hd : d ∈ Subgroup.normalizer (E : Set (MulAut V))) {f : MulAut V} (hf : f ∈ E) :
    d * f * d⁻¹ ∈ E :=
  (Subgroup.mem_normalizer_iff.mp hd f).mp hf

private theorem fix_normalizer_iff {E : Subgroup (MulAut V)} {d : MulAut V}
    (hd : d ∈ Subgroup.normalizer (E : Set (MulAut V))) (w : V) :
    d w ∈ Fix E ↔ w ∈ Fix E := by
  have hd' : d⁻¹ ∈ Subgroup.normalizer (E : Set (MulAut V)) := Subgroup.inv_mem _ hd
  rw [mem_fix_iff, mem_fix_iff]
  constructor
  · intro h f hf
    have h1 := h (d * f * d⁻¹) (conj_mem_of_normalizer hd hf)
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self] at h1
    have h2 : d⁻¹ (d (f w)) = d⁻¹ (d w) := congrArg (fun z => d⁻¹ z) h1
    rwa [MulAut.inv_apply_self, MulAut.inv_apply_self] at h2
  · intro h f hf
    have h1 := h (d⁻¹ * f * d⁻¹⁻¹) (conj_mem_of_normalizer hd' hf)
    rw [inv_inv, MulAut.mul_apply, MulAut.mul_apply] at h1
    have h2 : d (d⁻¹ (f (d w))) = d w := congrArg (fun z => d z) h1
    rwa [MulAut.apply_inv_self] at h2

private theorem map_conj_eq_of_normalizer {E : Subgroup (MulAut V)} {d : MulAut V}
    (hd : d ∈ Subgroup.normalizer (E : Set (MulAut V))) :
    E.map (MulAut.conj d).toMonoidHom = E := by
  have hd' : d⁻¹ ∈ Subgroup.normalizer (E : Set (MulAut V)) := Subgroup.inv_mem _ hd
  ext g
  constructor
  · intro hg
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hg
    rw [conj_hom_apply]
    exact conj_mem_of_normalizer hd hf
  · intro hg
    refine Subgroup.mem_map.mpr ⟨d⁻¹ * g * d⁻¹⁻¹, conj_mem_of_normalizer hd' hg, ?_⟩
    rw [conj_hom_apply]
    group

private theorem conjSub_le {E H : Subgroup (MulAut V)} {d : MulAut V}
    (hd : d ∈ Subgroup.normalizer (E : Set (MulAut V))) (hHE : H ≤ E) :
    conjSub d H ≤ E := by
  intro g hg
  obtain ⟨h, hh, rfl⟩ := mem_conjSub.mp hg
  exact conj_mem_of_normalizer hd (hHE hh)

private theorem conjSub_relIndex {E H : Subgroup (MulAut V)} {d : MulAut V}
    (hd : d ∈ Subgroup.normalizer (E : Set (MulAut V))) :
    (conjSub d H).relIndex E = H.relIndex E := by
  unfold conjSub
  have hinj : Function.Injective (MulAut.conj d).toMonoidHom :=
    fun a b hab => (MulAut.conj d).injective hab
  have h := Subgroup.relIndex_map_map_of_injective H E hinj
  rw [map_conj_eq_of_normalizer hd] at h
  exact h

private theorem conjSub_active {E H : Subgroup (MulAut V)} {d : MulAut V}
    (hd : d ∈ Subgroup.normalizer (E : Set (MulAut V))) (ha : ¬ Fix H ≤ Fix E) :
    ¬ Fix (conjSub d H) ≤ Fix E := by
  intro hle
  apply ha
  intro w hw
  have h1 : d w ∈ Fix (conjSub d H) := by
    rw [mem_fix_conjSub, MulAut.inv_apply_self]
    exact hw
  exact (fix_normalizer_iff hd w).mp (hle h1)

private theorem not_normalized_of_comm {E D : Subgroup (MulAut V)}
    (hE5 : ∀ x ∈ E, x ^ 5 = 1) (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hDE : D ≤ Subgroup.normalizer (E : Set (MulAut V))) {e : MulAut V} (heD : e ∈ ⁅D, D⁆)
    (hinv : ∀ y ∈ E, e * y * e⁻¹ = y⁻¹) {H : Subgroup (MulAut V)} (hHE : H ≤ E)
    (hH : H.relIndex E = 5) : ¬ ∀ d ∈ D, ∀ h ∈ H, d * h * d⁻¹ ∈ H := by
  intro hnorm
  obtain ⟨x, hxE, hxH⟩ := exists_mem_not_mem_of_relIndex hH
  have hx5 : x ^ 5 = 1 := hE5 x hxE
  have hx5z : x ^ (5 : ℤ) = 1 := by
    rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact hx5
  have hsup : H ⊔ Subgroup.zpowers x = E := hyper_sup_zpowers_eq hHE hH hxE hxH
  have hc : ∀ h ∈ H, h * x = x * h := fun h hh => hEab h (hHE hh) x hxE
  have hex : ∀ g ∈ D, ∃ k : ℤ, ∃ h ∈ H, g * x * g⁻¹ = h * x ^ k := by
    intro g hg
    have hmem : g * x * g⁻¹ ∈ H ⊔ Subgroup.zpowers x := by
      rw [hsup]
      exact conj_mem_of_normalizer (hDE hg) hxE
    obtain ⟨h, hh, k, hk⟩ := mem_sup_zpowers_of_comm hc hmem
    exact ⟨k, h, hh, hk⟩
  have hmul : ∀ (g g' : MulAut V) (k k' : ℤ) (h h' : MulAut V), g ∈ D → g' ∈ D → h ∈ H →
      h' ∈ H → g * x * g⁻¹ = h * x ^ k → g' * x * g'⁻¹ = h' * x ^ k' →
      ∃ h'' ∈ H, g * g' * x * (g * g')⁻¹ = h'' * x ^ (k * k') := by
    intro g g' k k' h h' hg hg' hh hh' hk hk'
    refine ⟨g * h' * g⁻¹ * h ^ k', H.mul_mem (hnorm g hg h' hh') (H.zpow_mem hh k'), ?_⟩
    have hcm : Commute h (x ^ k) := (show Commute h x from hc h hh).zpow_right k
    calc g * g' * x * (g * g')⁻¹ = g * (g' * x * g'⁻¹) * g⁻¹ := by group
      _ = g * (h' * x ^ k') * g⁻¹ := by rw [hk']
      _ = g * h' * g⁻¹ * (g * x * g⁻¹) ^ k' := by rw [conj_zpow]; group
      _ = g * h' * g⁻¹ * (h * x ^ k) ^ k' := by rw [hk]
      _ = g * h' * g⁻¹ * (h ^ k' * (x ^ k) ^ k') := by rw [hcm.mul_zpow]
      _ = g * h' * g⁻¹ * h ^ k' * x ^ (k * k') := by rw [← zpow_mul]; group
  have hfive : ∀ (m : ℤ) (h : MulAut V), h ∈ H → x = h * x ^ m → (5 : ℤ) ∣ 1 - m := by
    intro m h hh hm
    have hmem : x ^ (1 - m) ∈ H := by
      have heq : x ^ (1 - m) = h := by
        calc x ^ (1 - m) = x * (x ^ m)⁻¹ := by rw [zpow_sub, zpow_one]
          _ = h * x ^ m * (x ^ m)⁻¹ := by rw [← hm]
          _ = h := by group
      rw [heq]
      exact hh
    exact five_dvd_of_zpow_mem hx5 hxH hmem
  have hpow : ∀ k : ℤ, (5 : ℤ) ∣ 1 - k → x ^ k = x := by
    intro k hk
    obtain ⟨t, ht⟩ := hk
    have hk' : k = 1 + 5 * (-t) := by omega
    rw [hk', zpow_add, zpow_one, zpow_mul, hx5z, one_zpow, mul_one]
  have hcomm : ∀ d ∈ D, ∀ d' ∈ D, ∃ K : ℤ, (5 : ℤ) ∣ 1 - K ∧
      ∃ h ∈ H, ⁅d, d'⁆ * x * ⁅d, d'⁆⁻¹ = h * x ^ K := by
    intro d hd d' hd'
    obtain ⟨k₁, h₁, hh₁, hk₁⟩ := hex d hd
    obtain ⟨k₂, h₂, hh₂, hk₂⟩ := hex d' hd'
    obtain ⟨k₃, h₃, hh₃, hk₃⟩ := hex d⁻¹ (D.inv_mem hd)
    obtain ⟨k₄, h₄, hh₄, hk₄⟩ := hex d'⁻¹ (D.inv_mem hd')
    have h13 : (5 : ℤ) ∣ 1 - k₁ * k₃ := by
      obtain ⟨h₅, hh₅, hk₅⟩ := hmul d d⁻¹ k₁ k₃ h₁ h₃ hd (D.inv_mem hd) hh₁ hh₃ hk₁ hk₃
      simp only [mul_inv_cancel, one_mul, inv_one, mul_one] at hk₅
      exact hfive _ h₅ hh₅ hk₅
    have h24 : (5 : ℤ) ∣ 1 - k₂ * k₄ := by
      obtain ⟨h₆, hh₆, hk₆⟩ := hmul d' d'⁻¹ k₂ k₄ h₂ h₄ hd' (D.inv_mem hd') hh₂ hh₄ hk₂ hk₄
      simp only [mul_inv_cancel, one_mul, inv_one, mul_one] at hk₆
      exact hfive _ h₆ hh₆ hk₆
    have hK : (5 : ℤ) ∣ 1 - k₁ * k₂ * (k₃ * k₄) := by
      have hid : 1 - k₁ * k₂ * (k₃ * k₄) = (1 - k₁ * k₃) * (k₂ * k₄) + (1 - k₂ * k₄) := by
        ring
      rw [hid]
      exact dvd_add (dvd_mul_of_dvd_left h13 _) h24
    obtain ⟨h₇, hh₇, hk₇⟩ := hmul d d' k₁ k₂ h₁ h₂ hd hd' hh₁ hh₂ hk₁ hk₂
    obtain ⟨h₈, hh₈, hk₈⟩ :=
      hmul d⁻¹ d'⁻¹ k₃ k₄ h₃ h₄ (D.inv_mem hd) (D.inv_mem hd') hh₃ hh₄ hk₃ hk₄
    obtain ⟨h₉, hh₉, hk₉⟩ := hmul (d * d') (d⁻¹ * d'⁻¹) (k₁ * k₂) (k₃ * k₄) h₇ h₈
      (D.mul_mem hd hd') (D.mul_mem (D.inv_mem hd) (D.inv_mem hd')) hh₇ hh₈ hk₇ hk₈
    have hcd : ⁅d, d'⁆ = d * d' * (d⁻¹ * d'⁻¹) := by
      rw [commutatorElement_def]
      group
    refine ⟨k₁ * k₂ * (k₃ * k₄), hK, h₉, hh₉, ?_⟩
    rw [hcd]
    exact hk₉
  let R : Subgroup (MulAut V) :=
    { carrier := {g | g ∈ D ∧ ∃ h ∈ H, g * x * g⁻¹ = h * x}
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨ha1, h₁, hh₁, hk₁⟩ := ha
        obtain ⟨hb1, h₂, hh₂, hk₂⟩ := hb
        have hk₁' : a * x * a⁻¹ = h₁ * x ^ (1 : ℤ) := by rw [zpow_one]; exact hk₁
        have hk₂' : b * x * b⁻¹ = h₂ * x ^ (1 : ℤ) := by rw [zpow_one]; exact hk₂
        obtain ⟨h₃, hh₃, hk₃⟩ := hmul a b 1 1 h₁ h₂ ha1 hb1 hh₁ hh₂ hk₁' hk₂'
        refine ⟨D.mul_mem ha1 hb1, h₃, hh₃, ?_⟩
        rw [one_mul, zpow_one] at hk₃
        exact hk₃
      one_mem' := ⟨D.one_mem, 1, H.one_mem, by simp⟩
      inv_mem' := fun {a} ha => by
        obtain ⟨ha1, h₁, hh₁, hk₁⟩ := ha
        have hk₁' : a * x * a⁻¹ = h₁ * x ^ (1 : ℤ) := by rw [zpow_one]; exact hk₁
        obtain ⟨k', h', hh', hk'⟩ := hex a⁻¹ (D.inv_mem ha1)
        obtain ⟨h'', hh'', hk''⟩ :=
          hmul a a⁻¹ 1 k' h₁ h' ha1 (D.inv_mem ha1) hh₁ hh' hk₁' hk'
        simp only [mul_inv_cancel, one_mul, inv_one, mul_one] at hk''
        have hk5 : (5 : ℤ) ∣ 1 - k' := hfive _ h'' hh'' hk''
        exact ⟨D.inv_mem ha1, h', hh', by rw [hk', hpow k' hk5]⟩ }
  have hRmem : ∀ g, g ∈ R ↔ g ∈ D ∧ ∃ h ∈ H, g * x * g⁻¹ = h * x := fun g => Iff.rfl
  have hRcomm : ∀ d ∈ D, ∀ d' ∈ D, ⁅d, d'⁆ ∈ R := by
    intro d hd d' hd'
    obtain ⟨K, hK, h, hh, heq⟩ := hcomm d hd d' hd'
    refine (hRmem _).mpr ⟨?_, h, hh, ?_⟩
    · rw [commutatorElement_def]
      exact D.mul_mem (D.mul_mem (D.mul_mem hd hd') (D.inv_mem hd)) (D.inv_mem hd')
    · rw [heq, hpow K hK]
  have hRD : ⁅D, D⁆ ≤ R :=
    Subgroup.commutator_le.mpr fun d hd d' hd' => hRcomm d hd d' hd'
  obtain ⟨-, h, hh, heq⟩ := (hRmem e).mp (hRD heD)
  rw [hinv x hxE] at heq
  have hh' : h = x⁻¹ * x⁻¹ := by
    calc h = h * x * x⁻¹ := by group
      _ = x⁻¹ * x⁻¹ := by rw [← heq]
  rw [hh'] at hh
  have h2 : x * x ∈ H := by
    have := H.inv_mem hh
    rwa [mul_inv_rev, inv_inv] at this
  have hx5' : x * x * (x * x) * x = 1 := by
    rw [show x * x * (x * x) * x = x ^ 5 by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
    exact hx5
  have hx4 : x * x * (x * x) = x⁻¹ := eq_inv_of_mul_eq_one_left hx5'
  apply hxH
  have h3 : x⁻¹ ∈ H := by
    rw [← hx4]
    exact H.mul_mem h2 h2
  simpa using H.inv_mem h3

private theorem exists_three_active {E D : Subgroup (MulAut V)}
    (hE5 : ∀ x ∈ E, x ^ 5 = 1) (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hDE : D ≤ Subgroup.normalizer (E : Set (MulAut V))) {e : MulAut V} (heD : e ∈ ⁅D, D⁆)
    (hinv : ∀ y ∈ E, e * y * e⁻¹ = y⁻¹)
    (hD : ∀ D₀ : Subgroup (MulAut V), D₀ ≤ D → D₀.relIndex D ≤ 2 → D₀ = D)
    {H₁ : Subgroup (MulAut V)} (hH₁E : H₁ ≤ E) (hH₁ : H₁.relIndex E = 5)
    (ha₁ : ¬ Fix H₁ ≤ Fix E) :
    ∃ H₂ H₃ : Subgroup (MulAut V), H₂ ≤ E ∧ H₂.relIndex E = 5 ∧ ¬ Fix H₂ ≤ Fix E ∧
      H₃ ≤ E ∧ H₃.relIndex E = 5 ∧ ¬ Fix H₃ ≤ Fix E ∧
      H₁ ≠ H₂ ∧ H₁ ≠ H₃ ∧ H₂ ≠ H₃ := by
  have hconj : ∀ d ∈ D, conjSub d H₁ ≤ E ∧ (conjSub d H₁).relIndex E = 5 ∧
      ¬ Fix (conjSub d H₁) ≤ Fix E := fun d hd =>
    ⟨conjSub_le (hDE hd) hH₁E, by rw [conjSub_relIndex (hDE hd)]; exact hH₁,
      conjSub_active (hDE hd) ha₁⟩
  by_cases hall : ∀ d ∈ D, conjSub d H₁ = H₁
  · exfalso
    exact not_normalized_of_comm hE5 hEab hDE heD hinv hH₁E hH₁
      (fun d hd h hh => by rw [← hall d hd]; exact mem_conjSub.mpr ⟨h, hh, rfl⟩)
  push Not at hall
  obtain ⟨d₁, hd₁D, hd₁⟩ := hall
  by_cases hthird : ∃ b ∈ D, conjSub b H₁ ≠ H₁ ∧ conjSub b H₁ ≠ conjSub d₁ H₁
  · obtain ⟨b, hbD, hb1, hb2⟩ := hthird
    obtain ⟨hle₂, hi₂, ha₂⟩ := hconj d₁ hd₁D
    obtain ⟨hle₃, hi₃, ha₃⟩ := hconj b hbD
    exact ⟨conjSub d₁ H₁, conjSub b H₁, hle₂, hi₂, ha₂, hle₃, hi₃, ha₃,
      hd₁.symm, hb1.symm, hb2.symm⟩
  exfalso
  push Not at hthird
  have hstab : (stabSub D H₁).relIndex D = 2 := by
    rw [Subgroup.relIndex_eq_two_iff']
    refine ⟨d₁⁻¹, D.inv_mem hd₁D, fun b hbD => ?_⟩
    by_cases hb : conjSub b H₁ = H₁
    · have hbS : b ∈ stabSub D H₁ := mem_stabSub.mpr ⟨hbD, hb⟩
      have hnot : d₁⁻¹ * b ∉ stabSub D H₁ := by
        intro hmem
        have hc := (mem_stabSub.mp hmem).2
        rw [conjSub_mul, hb] at hc
        apply hd₁
        calc conjSub d₁ H₁ = conjSub d₁ (conjSub d₁⁻¹ H₁) := by rw [hc]
          _ = H₁ := conjSub_conjSub_inv d₁ H₁
      exact Or.inr ⟨hbS, hnot⟩
    · have hin : d₁⁻¹ * b ∈ stabSub D H₁ := by
        refine mem_stabSub.mpr ⟨D.mul_mem (D.inv_mem hd₁D) hbD, ?_⟩
        rw [conjSub_mul, hthird b hbD hb, conjSub_inv_conjSub d₁ H₁]
      have hout : b ∉ stabSub D H₁ := fun h => hb (mem_stabSub.mp h).2
      exact Or.inl ⟨hin, hout⟩
  have hEq := hD (stabSub D H₁) (fun g hg => (mem_stabSub.mp hg).1) hstab.le
  have hd₁mem : d₁ ∈ stabSub D H₁ := by
    rw [hEq]
    exact hd₁D
  exact hd₁ (mem_stabSub.mp hd₁mem).2

theorem exists_two_pow_twelve_core (hV : ∀ v : V, v * v = 1) {E D : Subgroup (MulAut V)}
    (hE5 : ∀ x ∈ E, x ^ 5 = 1) (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hEne : E ≠ ⊥)
    (hDE : D ≤ Subgroup.normalizer (E : Set (MulAut V))) {e : MulAut V} (heD : e ∈ ⁅D, D⁆)
    (hinv : ∀ y ∈ E, e * y * e⁻¹ = y⁻¹)
    (hD : ∀ D₀ : Subgroup (MulAut V), D₀ ≤ D → D₀.relIndex D ≤ 2 → D₀ = D) :
    ∃ y ∈ E, 2 ^ 12 ≤ (Fix (Subgroup.zpowers y)).index := by
  obtain ⟨H₁, hH₁E, hH₁, ha₁⟩ := exists_active_hyper hV hE5 hEab hEne
  obtain ⟨H₂, H₃, hH₂E, hH₂, ha₂, hH₃E, hH₃, ha₃, h12, h13, h23⟩ :=
    exists_three_active hE5 hEab hDE heD hinv hD hH₁E hH₁ ha₁
  exact exists_two_pow_twelve_of_three hV hE5 hEab hH₁E hH₁ hH₂E hH₂ hH₃E hH₃ h12 h13 h23
    ha₁ ha₂ ha₃

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
